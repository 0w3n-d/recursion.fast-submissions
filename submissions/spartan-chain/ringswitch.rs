//! Ring switching (BLUEPRINT-R1 §4.3, leanVM paper Annex A with `κ_pack = 6`; stage order as in
//! leanVM `crates/pcs/src/ring_switch.rs`, pin `a386121f`, written fresh):
//! `a_0 = a`, `a_{p+1} = a_p + f_p · a_p^{2^{M_p}}`, `M_p = 2^{5−p}`, `Φ(a) = a_6`;
//! equivalently `Φ(a) = Σ_{k<64} c_k a^{2^k}`.

use crate::field::{E, K};

pub const STAGES: usize = 6;

/// `Φ` by the six stages (63 squarings, 6 multiplications).
pub fn phi(f: &[E; STAGES], a: E) -> E {
    let mut a = a;
    for p in 0..STAGES {
        let mp = 1usize << (5 - p);
        a += f[p] * a.frob(mp);
    }
    a
}

/// The table `c_k`, `k < 64`: `T_0 = {0 ↦ 1}`,
/// `T_{p+1} = T_p ∪ { k + M_p ↦ f_p · T_p[k]^{2^{M_p}} }`.
pub fn coeffs(f: &[E; STAGES]) -> [E; 64] {
    let mut c = [E::ZERO; 64];
    c[0] = E::ONE;
    let mut present = vec![0usize];
    for p in 0..STAGES {
        let mp = 1usize << (5 - p);
        let cur = present.clone();
        for &k in &cur {
            c[k + mp] = f[p] * c[k].frob(mp);
            present.push(k + mp);
        }
    }
    c
}

/// `Φ` as an `F₂`-linear map through 24 byte tables (the prover's bulk application).
pub struct PhiTab {
    t: Vec<E>, // [byte position 0..24][byte 0..256]
}

impl PhiTab {
    pub fn new(f: &[E; STAGES]) -> PhiTab {
        let mut t = vec![E::ZERO; 24 * 256];
        for pos in 0..24 {
            let mut img = [E::ZERO; 8];
            for b in 0..8 {
                let mut e = E::ZERO;
                e.0[pos / 8] = 1u64 << (8 * (pos % 8) + b);
                img[b] = phi(f, e);
            }
            for v in 1..256usize {
                let low = v.trailing_zeros() as usize;
                t[pos * 256 + v] = t[pos * 256 + (v & (v - 1))] + img[low];
            }
        }
        PhiTab { t }
    }
    #[inline]
    pub fn apply(&self, a: E) -> E {
        let mut r = E::ZERO;
        for pos in 0..24 {
            let byte = ((a.0[pos / 8] >> (8 * (pos % 8))) & 255) as usize;
            r += self.t[pos * 256 + byte];
        }
        r
    }
}

/// The target `T = Σ_i x^i Φ(s_i)`.
pub fn target(f: &[E; STAGES], slices: &[E]) -> E {
    let mut acc = E::ZERO;
    for (i, &s) in slices.iter().enumerate() {
        acc += phi(f, s).mul_k(K(1u64 << i));
    }
    acc
}

/// `W̃(r'') = Σ_k c_k eq(r_hi^{2^k}, r'')`.
pub fn weight_mle(c: &[E; 64], r_hi: &[E], r2: &[E]) -> E {
    let mut acc = E::ZERO;
    let mut pw: Vec<E> = r_hi.to_vec();
    for k in 0..64 {
        if k > 0 {
            for x in pw.iter_mut() {
                *x = x.sq();
            }
        }
        let mut e = E::ONE;
        for l in 0..r2.len() {
            e *= E::ONE + pw[l] + r2[l];
        }
        acc += c[k] * e;
    }
    acc
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mle::{eq_table, mle_eval};

    fn rnd(s: &mut u64) -> E {
        let mut nx = || {
            *s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            *s
        };
        E([nx(), nx(), nx()])
    }

    #[test]
    fn phi_forms_agree() {
        let mut s = 3;
        let f: [E; 6] = std::array::from_fn(|_| rnd(&mut s));
        let c = coeffs(&f);
        let tab = PhiTab::new(&f);
        for _ in 0..20 {
            let a = rnd(&mut s);
            let mut sum = E::ZERO;
            for k in 0..64 {
                sum += c[k] * a.frob(k);
            }
            assert_eq!(phi(&f, a), sum);
            assert_eq!(tab.apply(a), sum);
        }
        // controls: all f_p = 0 is the identity; one f_p ≠ 0 is not
        let z = [E::ZERO; 6];
        let a = rnd(&mut s);
        assert_eq!(phi(&z, a), a);
        let mut one = z;
        one[3] = E::ONE;
        assert_ne!(phi(&one, a), a);
    }

    /// L-R3 and L-R4 on a small instance: `Σ_u Φ(eq(r,u)) q(u) = Σ_i x^i Φ(Q̃_i(r))` and
    /// `W̃(r'') = Σ_k c_k eq(r^{2^k}, r'')`.
    #[test]
    fn ring_switch_identities() {
        let mut s = 11;
        let f: [E; 6] = std::array::from_fn(|_| rnd(&mut s));
        let l = 4;
        let q: Vec<u64> = (0..16u64).map(|i| i.wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ 0x55).collect();
        let r: Vec<E> = (0..l).map(|_| rnd(&mut s)).collect();
        let eq = eq_table(&r);
        let mut lhs = E::ZERO;
        for u in 0..16 {
            lhs += phi(&f, eq[u]).mul_k(K(q[u]));
        }
        let slices: Vec<E> = (0..64)
            .map(|i| {
                let mut acc = E::ZERO;
                for u in 0..16 {
                    if (q[u] >> i) & 1 == 1 {
                        acc += eq[u];
                    }
                }
                acc
            })
            .collect();
        assert_eq!(lhs, target(&f, &slices));
        let w: Vec<E> = eq.iter().map(|&e| phi(&f, e)).collect();
        let r2: Vec<E> = (0..l).map(|_| rnd(&mut s)).collect();
        assert_eq!(mle_eval(&w, &r2), weight_mle(&coeffs(&f), &r, &r2));
    }
}
