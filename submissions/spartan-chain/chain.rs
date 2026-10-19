//! The chain R1CS (BLUEPRINT-R1 §2.3–§2.4): shape, honest witness, `Az/Bz/Cz` bit tables, `pub`,
//! and the verifier's closed-form `M̃ρ(r_x, r_y)`.

use crate::blake2s::{chain_step, Digest};
use crate::circuit::{Circuit, BLOCK, CPOS};
use crate::field::E;
use crate::mle::{eq_at, eq_ee, eq_table};
use crate::par;

pub const CHAIN_CAP: u64 = 1 << 20;
pub const PROOF_CAP: usize = 1 << 20;
pub const T_COLS: usize = 260;

/// Everything sized by `n` (§2.3, §5.2, §6.1, §7).
#[derive(Clone, Copy, Debug)]
pub struct Shape {
    pub n: u64,
    pub kappa: usize,
    /// `log |w| = 14 + κ`
    pub lw: usize,
    /// `ℓ_x = ℓ_y = 15 + κ`
    pub ell: usize,
    pub mu_r: usize,
    pub lk: usize,
    pub ln: usize,
    pub m: usize,
    pub k: usize,
    pub nn: usize,
    /// column indices per squeeze answer, `⌊256/ℓ_N⌋`
    pub cnt: usize,
}

pub fn kappa_of(n: u64) -> usize {
    if n <= 1 {
        0
    } else {
        64 - (n - 1).leading_zeros() as usize
    }
}

impl Shape {
    pub fn new(n: u64) -> Shape {
        assert!(n >= 1 && n <= CHAIN_CAP);
        let kappa = kappa_of(n);
        let mu_r = (kappa + 3) / 2;
        let lk = 8 + kappa - mu_r;
        let ln = lk + 3;
        Shape {
            n,
            kappa,
            lw: 14 + kappa,
            ell: 15 + kappa,
            mu_r,
            lk,
            ln,
            m: 1 << mu_r,
            k: 1 << lk,
            nn: 1 << ln,
            cnt: 256 / ln,
        }
    }
    /// `8 + κ`, the packed witness's variables.
    pub fn lq(&self) -> usize {
        8 + self.kappa
    }
    pub fn blocks(&self) -> usize {
        1 << self.kappa
    }
    pub fn snark_size(&self) -> usize {
        31 + 48 * self.k + 96 * self.ell + 72 + 72 * self.ell + 1536 + 72 * self.lq()
            + T_COLS * (8 * self.m + 31 * self.ln)
    }
}

/// `leafSize n` (§7).
pub fn leaf_size(n: u64) -> usize {
    if n == 0 {
        80
    } else {
        80 + Shape::new(n).snark_size()
    }
}

/// The honest witness and the bit tables of `Az`, `Bz`, `Cz` (each `2^ℓ` bits).
pub struct Witness {
    /// `w`, `2^{14+κ}` bits; also the packed witness `q` (word `u'` is `q(u')`, §4.1).
    pub w: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub c: Vec<u64>,
    pub h: Digest,
}

#[inline]
pub fn get_bit(v: &[u64], i: usize) -> bool {
    (v[i >> 6] >> (i & 63)) & 1 == 1
}
#[inline]
fn set_bit(v: &mut [u64], i: usize, b: bool) {
    if b {
        v[i >> 6] |= 1u64 << (i & 63);
    }
}
#[inline]
pub fn digest_bit(d: &Digest, j: usize) -> bool {
    (d[j / 8] >> (j % 8)) & 1 == 1
}

/// `chainWitness s n` (§2.3, L-C3) and its tables. Block `t < 2^κ` hashes `chainEnd s t`.
pub fn witness(circ: &Circuit, sh: &Shape, s: &Digest) -> Witness {
    let nb = sh.blocks();
    let mut msgs = Vec::with_capacity(nb + 1);
    msgs.push(*s);
    for t in 0..nb {
        let next = chain_step(&msgs[t]);
        msgs.push(next);
    }
    let h = msgs[sh.n as usize];
    let words_w = 1usize << (sh.lw - 6);
    let words = 1usize << (sh.ell - 6);
    let mut w = vec![0u64; words_w];
    let mut a = vec![0u64; words];
    let mut b = vec![0u64; words];
    let mut c = vec![0u64; words];
    // region 0: one block per 256 words
    {
        let wc = &mut w[..];
        let ac = &mut a[..words_w];
        let bc = &mut b[..words_w];
        // fill blocks in parallel: split all three slices into 256-word blocks
        let mut blocks: Vec<(&mut [u64], &mut [u64], &mut [u64])> = wc
            .chunks_mut(256)
            .zip(ac.chunks_mut(256))
            .zip(bc.chunks_mut(256))
            .map(|((x, y), z)| (x, y, z))
            .collect();
        par::for_each_chunk_mut(&mut blocks, 4, |off, chunk| {
            let mut vals = Vec::new();
            for (i, (zw, aw, bw)) in chunk.iter_mut().enumerate() {
                let t = off + i;
                let (z, az, bz) = circ.trace(&msgs[t], &mut vals);
                zw.copy_from_slice(&z);
                aw.copy_from_slice(&az);
                bw.copy_from_slice(&bz);
            }
        });
    }
    c[..words_w].copy_from_slice(&w);
    // region 2 (xtop = 1): wiring rows j + 256 t, tail rows 2^{8+κ} + j
    let base = 1usize << sh.lw;
    for t in 0..nb {
        for j in 0..256 {
            let bit = digest_bit(&msgs[t], j);
            let x = base + j + 256 * t;
            set_bit(&mut a, x, bit);
            set_bit(&mut b, x, true);
            set_bit(&mut c, x, bit);
        }
    }
    for j in 0..256 {
        let x = base + (1usize << (8 + sh.kappa)) + j;
        let bit = digest_bit(&h, j);
        set_bit(&mut a, x, bit);
        set_bit(&mut b, x, true);
        set_bit(&mut c, x, bit);
    }
    Witness { w, a, b, c, h }
}

/// `Sat`, checked row by row on the bit tables (debug and tests): `A·B = C` everywhere, and the
/// tables are those of `z = (w ‖ pub)` for the region-2 rows.
pub fn sat_tables(wit: &Witness) -> bool {
    wit.a.iter().zip(&wit.b).zip(&wit.c).all(|((a, b), c)| a & b == *c)
}

/// The public column `pub(u)`: `pub(0) = 1`, `pub(1 + j) = s_j`, `pub(257 + j) = h_j`.
pub fn pub_bit(s: &Digest, h: &Digest, u: usize) -> bool {
    match u {
        0 => true,
        1..=256 => digest_bit(s, u - 1),
        257..=512 => digest_bit(h, u - 257),
        _ => false,
    }
}

/// `pub̃(r_u)` (§3): the 10-variable table of `r_u[0..10)` times `∏_{l ≥ 10} (1 + r_u[l])`.
pub fn pub_mle(s: &Digest, h: &Digest, r_u: &[E]) -> E {
    let t = eq_table(&r_u[..10]);
    let mut acc = E::ZERO;
    for u in 0..513 {
        if pub_bit(s, h, u) {
            acc += t[u];
        }
    }
    let mut f = E::ONE;
    for &r in &r_u[10..] {
        f *= E::ONE + r;
    }
    acc * f
}

/// `S̃(a, b)` (§2.4.1): the MLE of `[t' + 1 = t]` with `a ↔ t`, `b ↔ t'`.
pub fn shift_mle(a: &[E], b: &[E]) -> E {
    let kk = a.len();
    let mut acc = E::ZERO;
    for i in 0..kk {
        let mut term = (E::ONE + b[i]) * a[i];
        for l in 0..i {
            term *= b[l] * (E::ONE + a[l]);
        }
        for l in i + 1..kk {
            term *= E::ONE + a[l] + b[l];
        }
        acc += term;
    }
    acc
}

/// The row-factor scalars of §2.4 and the 8-variable table, shared by `V` and the prover.
pub struct RowFactors {
    pub r0: E,
    pub rw: E,
    pub rt: E,
    pub t0: E,
    /// `eq(r_kj, ·)`, 256 entries
    pub ekj: Vec<E>,
    /// `e = eq(r_k, ·)`, `2^14` entries
    pub e: Vec<E>,
}

pub fn row_factors(sh: &Shape, r_x: &[E]) -> RowFactors {
    let kp = sh.kappa;
    let xtop = r_x[14 + kp];
    let mut rw = xtop;
    for l in 8 + kp..14 + kp {
        rw *= E::ONE + r_x[l];
    }
    let mut rt = xtop * r_x[8 + kp];
    for l in 8..8 + kp {
        rt *= E::ONE + r_x[l];
    }
    for l in 9 + kp..14 + kp {
        rt *= E::ONE + r_x[l];
    }
    let mut t0 = E::ONE;
    for l in 8..8 + kp {
        t0 *= E::ONE + r_x[l];
    }
    RowFactors { r0: E::ONE + xtop, rw, rt, t0, ekj: eq_table(&r_x[..8]), e: eq_table(&r_x[..14]) }
}

/// `M̃ρ(r_x, r_y) = Ã + ρB̃ + ρ²C̃` by the formulas of §2.4 (the verifier's computation).
pub fn matrix_eval(circ: &Circuit, sh: &Shape, r_x: &[E], r_y: &[E], rho: E) -> E {
    let kp = sh.kappa;
    let rf = row_factors(sh, r_x);
    let r_t = &r_x[14..14 + kp];
    let r_t2 = &r_x[8..8 + kp];
    let r_j = &r_y[..14];
    let r_tp = &r_y[14..14 + kp];
    let ytop = r_y[14 + kp];
    let wt = eq_table(r_j);
    let (a0, b0) = circ.walk(&rf.e, &wt, true);
    let sig = |b: usize| -> E {
        let mut acc = E::ZERO;
        for j in 0..256 {
            acc += rf.ekj[j] * wt[b + j];
        }
        acc
    };
    let s256 = sig(256);
    let s1 = sig(1);
    let s648 = sig(648);
    let s257 = sig(257);
    let mut t0p = E::ONE;
    for &r in r_tp {
        t0p *= E::ONE + r;
    }
    let u0 = wt[0] * t0p;
    let eqtt = eq_ee(r_t, r_tp);
    let shift = shift_mle(r_t2, r_tp);
    let eqt2 = eq_ee(r_t2, r_tp);
    let eqn = eq_at(r_tp, sh.n - 1);
    let eqkj = eq_ee(&r_x[..14], r_j);
    let ny = E::ONE + ytop;
    let e512 = rf.e[CPOS];
    let at = rf.r0 * (ny * eqtt * a0 + ytop * e512 * u0)
        + rf.rw * (ny * shift * s256 + ytop * rf.t0 * t0p * s1)
        + rf.rt * (ny * eqn * s256);
    let bt = rf.r0 * (ny * eqtt * b0 + ytop * e512 * u0) + rf.rw * ytop * u0 + rf.rt * ytop * u0;
    let ct = rf.r0 * (ny * eqtt * eqkj) + rf.rw * (ny * eqt2 * s648) + rf.rt * (ytop * t0p * s257);
    at + rho * bt + rho * rho * ct
}

/// The dense table `M̃ρ(r_x, y)` over every `y`, built row by row from §2.3 (tests and the
/// known-answer harness only: quadratic in the block).
pub fn matrix_table_naive(circ: &Circuit, sh: &Shape, r_x: &[E], rho: E) -> Vec<E> {
    // Build A, B, C entries row by row from the definitions of §2.3.
    let rows = circ.row_bitsets();
    let eqx = eq_table(r_x);
    let lw = sh.lw;
    let nb = sh.blocks();
    let mut m = vec![E::ZERO; 1 << sh.ell];
    let pubcol = |u: usize| (1usize << lw) + u;
    let wcol = |t: usize, k: usize| k + BLOCK * t;
    for t in 0..nb {
        for k in 0..BLOCK {
            let x = k + BLOCK * t;
            let wx = eqx[x];
            if k == CPOS {
                m[pubcol(0)] += wx;
                m[pubcol(0)] += rho * wx;
            } else {
                let (ra, rb) = &rows[k];
                for j in 0..BLOCK {
                    if (ra[j / 64] >> (j % 64)) & 1 == 1 {
                        m[wcol(t, j)] += wx;
                    }
                    if (rb[j / 64] >> (j % 64)) & 1 == 1 {
                        m[wcol(t, j)] += rho * wx;
                    }
                }
            }
            m[wcol(t, k)] += rho * rho * wx;
        }
    }
    let base = 1usize << lw;
    for t in 0..nb {
        for j in 0..256 {
            let wx = eqx[base + j + 256 * t];
            if t >= 1 {
                m[wcol(t - 1, 256 + j)] += wx;
            } else {
                m[pubcol(1 + j)] += wx;
            }
            m[pubcol(0)] += rho * wx;
            m[wcol(t, 648 + j)] += rho * rho * wx;
        }
    }
    for j in 0..256 {
        let wx = eqx[base + (1 << (8 + sh.kappa)) + j];
        m[wcol(sh.n as usize - 1, 256 + j)] += wx;
        m[pubcol(0)] += rho * wx;
        m[pubcol(257 + j)] += rho * rho * wx;
    }
    m
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mle::mle_eval;

    #[test]
    fn shapes_and_sizes() {
        assert_eq!(leaf_size(16), 143_711);
        assert_eq!(leaf_size(1), 95_719);
        assert_eq!(leaf_size(64), 193_467);
        assert_eq!(leaf_size(1024), 457_843);
        assert_eq!(leaf_size(2048), 591_203);
        assert_eq!(leaf_size(1 << 14), 1_464_107);
        let sh = Shape::new(16);
        assert_eq!((sh.kappa, sh.m, sh.k, sh.nn), (4, 8, 512, 4096));
    }

    #[test]
    fn shift_is_the_boolean_shift() {
        for kk in 1..4usize {
            for t in 0..(1usize << kk) {
                for tp in 0..(1usize << kk) {
                    let a: Vec<E> = (0..kk).map(|l| E::from_bit((t >> l) & 1 == 1)).collect();
                    let b: Vec<E> = (0..kk).map(|l| E::from_bit((tp >> l) & 1 == 1)).collect();
                    assert_eq!(shift_mle(&a, &b), E::from_bit(tp + 1 == t));
                }
            }
        }
    }

    #[test]
    fn honest_witness_satisfies_and_wrong_bit_fails() {
        let circ = Circuit::build();
        for n in [1u64, 2, 3] {
            let sh = Shape::new(n);
            let s: Digest = std::array::from_fn(|i| i as u8);
            let wit = witness(&circ, &sh, &s);
            assert!(sat_tables(&wit));
            assert_eq!(wit.h, crate::blake2s::chain_end(&s, n));
            let mut bad = Witness { w: wit.w.clone(), a: wit.a.clone(), b: wit.b.clone(), c: wit.c.clone(), h: wit.h };
            bad.c[5] ^= 1 << 3; // C = z: one wrong witness bit
            assert!(!sat_tables(&bad));
        }
    }

    /// The closed form of §2.4 equals the MLE of the matrices built row by row from §2.3.
    #[test]
    fn matrix_formula_matches_definition() {
        let circ = Circuit::build();
        let mut s = 5u64;
        let mut nx = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        for n in [1u64, 2] {
            let sh = Shape::new(n);
            let r_x: Vec<E> = (0..sh.ell).map(|_| E([nx(), nx(), nx()])).collect();
            let r_y: Vec<E> = (0..sh.ell).map(|_| E([nx(), nx(), nx()])).collect();
            let rho = E([nx(), nx(), nx()]);
            let tab = matrix_table_naive(&circ, &sh, &r_x, rho);
            assert_eq!(mle_eval(&tab, &r_y), matrix_eval(&circ, &sh, &r_x, &r_y, rho), "n = {n}");
        }
    }
}
