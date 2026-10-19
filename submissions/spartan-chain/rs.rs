//! The Reed–Solomon code of the PCS (BLUEPRINT-R1 §5.1): domain `ω_c` = the `K` element whose word
//! is `c`; unnormalised subspace polynomials `W_0 = X`, `W_{i+1} = W_i (W_i + κ_i)`,
//! `κ_i = W_i(ω_{2^i})`; basis `X_j = ∏_i W_i^{bit_i(j)}`; `Enc(msg)_c = Σ_j msg_j X_j(ω_c)`.
//!
//! The prover encodes with the additive FFT of Lin–Chung–Han (LCH14) in this basis (the
//! structure of leanVM `crates/pcs/src/ntt/additive_ntt_f64.rs`, pin `a386121f`, adapted to the
//! unnormalised `W_i`, written fresh): to evaluate `p = p0 + W_{L-1} p1` on `θ + V_L`, the two
//! halves are `q0 = p0 + W_{L-1}(θ) p1` on `θ + V_{L-1}` and `q1 = q0 + κ_{L-1} p1` on
//! `θ + β_{L-1} + V_{L-1}` (`W_{L-1}` is `F₂`-linear and vanishes on `V_{L-1}`).

use crate::field::{KTab, E, K};

pub struct Code {
    pub lk: usize,
    pub ln: usize,
    /// `κ_i`, `i < ln`
    pub kap: Vec<K>,
    /// `wb[i][l] = W_i(β_l)`, `β_l = x^l`, `i ≤ lk`, `l < ln`
    wb: Vec<Vec<K>>,
    kap_tab: Vec<KTab>,
}

impl Code {
    pub fn new(lk: usize, ln: usize) -> Code {
        let mut kap = Vec::with_capacity(ln);
        for i in 0..ln {
            // W_i(β_i) by the recursion on values
            let mut w = K(1u64 << i);
            for j in 0..i {
                w = w * (w + kap[j]);
            }
            kap.push(w);
        }
        let mut wb = vec![vec![K::ZERO; ln]; lk + 1];
        for l in 0..ln {
            let mut w = K(1u64 << l);
            for i in 0..=lk {
                wb[i][l] = w;
                if i < ln {
                    w = w * (w + kap[i]);
                }
            }
        }
        let kap_tab = (0..lk).map(|i| KTab::new(kap[i])).collect();
        Code { lk, ln, kap, wb, kap_tab }
    }

    /// `W_i(ω_v)` for `i ≤ lk`, by linearity.
    fn w_at(&self, i: usize, v: usize) -> K {
        let mut acc = 0u64;
        let mut v = v;
        let mut l = 0;
        while v != 0 {
            if v & 1 == 1 {
                acc ^= self.wb[i][l].0;
            }
            v >>= 1;
            l += 1;
        }
        K(acc)
    }

    /// The tensor `(X_j(ω_c))_{j<k}` at one domain point (`V`'s computation, §5.1): the values
    /// `W_i(ω_c)` by the recursion (`i` multiplications each), then `k − 1` products.
    pub fn basis_at(&self, c: usize) -> Vec<K> {
        let k = 1usize << self.lk;
        let mut ws = Vec::with_capacity(self.lk);
        let mut w = K(c as u64);
        for i in 0..self.lk {
            ws.push(w);
            w = w * (w + self.kap[i]);
        }
        let mut x = vec![K::ZERO; k];
        x[0] = K::ONE;
        for i in 0..self.lk {
            let h = 1usize << i;
            for j in 0..h {
                x[j + h] = x[j] * ws[i];
            }
        }
        x
    }

    /// `Enc(msg)_c` for `msg ∈ E^k` given the tensor at `c`.
    pub fn enc_at(msg: &[E], basis: &[K]) -> E {
        let mut acc = E::ZERO;
        for j in 0..msg.len() {
            acc += msg[j].mul_k(basis[j]);
        }
        acc
    }

    /// `Enc(msg)` for `msg ∈ K^k`, all `N = 2^ln` points, by the additive FFT on the `N/k` cosets.
    pub fn encode_k(&self, msg: &[K]) -> Vec<K> {
        let k = 1usize << self.lk;
        let nn = 1usize << self.ln;
        assert_eq!(msg.len(), k);
        let mut out = vec![K::ZERO; nn];
        for (ch, buf) in out.chunks_mut(k).enumerate() {
            buf.copy_from_slice(msg);
            self.fft(buf, ch * k);
        }
        out
    }

    fn fft(&self, a: &mut [K], off: usize) {
        let k = a.len();
        for i in (0..self.lk).rev() {
            let half = 1usize << i;
            let kt = &self.kap_tab[i];
            let mut s = 0;
            while s < k {
                let w = self.w_at(i, off + s);
                let (lo, hi) = a[s..s + 2 * half].split_at_mut(half);
                for j in 0..half {
                    let h = hi[j];
                    let l2 = lo[j] + w * h;
                    lo[j] = l2;
                    hi[j] = K(l2.0 ^ kt.mul(h.0));
                }
                s += 2 * half;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fft_matches_naive_encoding() {
        for (lk, ln) in [(2usize, 5usize), (4, 7), (7, 10)] {
            let code = Code::new(lk, ln);
            let k = 1 << lk;
            let msg: Vec<K> = (0..k).map(|i| K((i as u64 + 1).wrapping_mul(0x9E37_79B9_7F4A_7C15))).collect();
            let enc = code.encode_k(&msg);
            let msg_e: Vec<E> = msg.iter().map(|&x| E::from_k(x)).collect();
            for c in 0..(1 << ln) {
                assert_eq!(E::from_k(enc[c]), Code::enc_at(&msg_e, &code.basis_at(c)), "c = {c}");
            }
        }
    }

    /// `X_j` has degree `j` and is monic: `Enc` of `e_j` agrees with the polynomial `X_j`
    /// computed by naive polynomial arithmetic, and a nonzero message has a nonzero codeword.
    #[test]
    fn basis_is_the_subspace_basis() {
        let code = Code::new(2, 5);
        // W_1(X) = X (X + 1) since κ_0 = W_0(β_0) = 1
        assert_eq!(code.kap[0], K::ONE);
        for c in 0..32usize {
            let w = K(c as u64);
            let b = code.basis_at(c);
            assert_eq!(b[1], w);
            assert_eq!(b[2], w * (w + K::ONE));
            assert_eq!(b[3], w * w * (w + K::ONE));
        }
        let msg = vec![K::ZERO, K::ZERO, K(5), K::ZERO];
        assert!(code.encode_k(&msg).iter().any(|x| *x != K::ZERO));
    }
}
