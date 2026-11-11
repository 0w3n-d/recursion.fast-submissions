//! The two links (BLUEPRINT §4.1–4.2; the schedule's `CHlink`/`KSlink` phases, WP-0's [model] shapes), as sent
//! to WP-11a/WP-8 (docs/lvm/stages/WP-15a.md). Each is one degree-2 sumcheck over the rows whose target is
//! public, followed by the column values at its point; `verify_*` replays the verifier's arithmetic (a test
//! oracle; the Lean `V_S` is normative).
//!
//! **CH** (`in_{k} = Pad43(Y_{k−1})` for `1 ≤ k < N`). Challenges `ρ ∈ E^logN, λ ∈ E^3, ζ ∈ E^6`;
//! `ω(l,p) = eq(λ,l)·eq(ζ,p)` on `in` lanes `l < 8`. Summand `S(ρ,k)·g(k) + E'(ρ,k)·h_Y(k)`, target
//! `C(ω)·(1 + eq(ρ,1⃗))`; then the 64 `in` slices at `(ρ', λ, 0,0,0)`, a ring switch, a 2-round sumcheck over the
//! `Y` lane bits, the 64 `Y` slices at `(ρ', μ, 1,0,1,1)` (slot `52 + m`), a ring switch, 5 unused lane samples.
//! The constant lanes 8–24 of `in` become 17 word claims at `(ρ', slot l)`.
//!
//! **KS** (`in_i = cont_i·Y_{i−1} + [l<17]·Msg_i`). Challenges `ρ ∈ E^ks, λ ∈ E^5`, `ω_l = eq(λ,l)`. Summand
//! `Sc(ρ,k)·Y^ω(k) + eq(ρ,k)·(in^ω(k) + Msg^ω(k))`, target 0; then `Y^ω, in^ω, M^ω, X^ω` at `ρ'`.

use crate::lv::fiat_shamir::transcript::ProverState;
use crate::lv::pcs::ring_switch::fold_1b_rows;
use crate::lv::primitives::field::{F64, F192};
use crate::lv::primitives::multilinear::{eq_eval, eq_table};
use crate::lvm::params::{LANE_BITS, LANES, RING_STAGES, REC_STREAM_COLS};
use crate::lvm::tables::{Chain, Layout, Sponge};

/// A claim on a commitment, prover side: either a combination of aligned point evaluations with one value
/// (`Σ_t coeff_t · f̃_{offset_t}(point_t) = value`), or a ring-switched claim on the 64 bit slices of the
/// aligned block at `offset` at `point`, with its own map challenges.
#[derive(Clone, Debug)]
pub enum Claim {
    Point { terms: Vec<(usize, Vec<F192>, F192)>, value: F192 },
    Ring { offset: usize, point: Vec<F192>, slices: Vec<F192>, map: [F192; RING_STAGES] },
}

impl Claim {
    pub fn point(offset: usize, point: Vec<F192>, value: F192) -> Self {
        Claim::Point { terms: vec![(offset, point, F192::ONE)], value }
    }
}

fn e(x: u64) -> F192 {
    F192::new(x, 0, 0)
}

/// Bit weights as byte tables: `t[b][v] = Σ_{j<8} w[8b + j]·bit_j(v)`.
pub fn byte_tables(w: &[F192; 64]) -> Vec<[F192; 256]> {
    (0..8)
        .map(|b| {
            let mut t = [F192::ZERO; 256];
            for v in 1..256usize {
                let low = v & v.wrapping_neg();
                t[v] = t[v ^ low] + w[8 * b + low.trailing_zeros() as usize];
            }
            t
        })
        .collect()
}

#[inline]
fn bitdot(t: &[[F192; 256]], x: u64) -> F192 {
    let mut acc = F192::ZERO;
    for (b, tb) in t.iter().enumerate() {
        acc += tb[((x >> (8 * b)) & 255) as usize];
    }
    acc
}

/// One round of a degree-2 sumcheck of `Σ_k a(k)b(k) + c(k)d(k)`, variable 0 first: `(q(0), q₂)`.
fn round(t: [&[F192]; 4]) -> (F192, F192) {
    let half = t[0].len() / 2;
    crate::lv::parallel::fold_reduce(
        half,
        || (F192::ZERO, F192::ZERO),
        |acc, j| {
            let [a, b, c, d] = t;
            let (a0, a1, b0, b1) = (a[2 * j], a[2 * j + 1], b[2 * j], b[2 * j + 1]);
            let (c0, c1, d0, d1) = (c[2 * j], c[2 * j + 1], d[2 * j], d[2 * j + 1]);
            acc.0 += a0 * b0 + c0 * d0;
            acc.1 += (a0 + a1) * (b0 + b1) + (c0 + c1) * (d0 + d1);
        },
        |x, y| (x.0 + y.0, x.1 + y.1),
    )
}

fn fold(v: &mut Vec<F192>, r: F192) {
    let half = v.len() / 2;
    let next: Vec<F192> = crate::lv::parallel::map_collect(half, |j| v[2 * j] + r * (v[2 * j] + v[2 * j + 1]));
    *v = next;
}

/// The plain degree-2 sumcheck of `Σ a·b + c·d` from `claim`: sends `(c₀, c₂)` per round (the Lean
/// `sumcheck _ 3`), returns the point and the final claim.
pub fn sumcheck2(ps: &mut ProverState, mut t: [Vec<F192>; 4], mut claim: F192) -> (Vec<F192>, F192, [F192; 4]) {
    let n = t[0].len().trailing_zeros() as usize;
    let mut point = Vec::with_capacity(n);
    for _ in 0..n {
        let (c0, c2) = round([&t[0], &t[1], &t[2], &t[3]]);
        let c1 = claim + c2; // q(0) + q(1) = c1 + c2 in characteristic 2
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        for v in t.iter_mut() {
            fold(v, r);
        }
        point.push(r);
    }
    (point, claim, [t[0][0], t[1][0], t[2][0], t[3][0]])
}

/// The MLE of the non-cyclic shift `S(x, y) = Σ_{i ≤ 2^n − 2} eq(x, i)·eq(i + 1, y)`, little-endian:
/// `Σ_j Π_{t<j} x_t (1 + y_t) · (1 + x_j) y_j · Π_{t>j} (1 + x_t + y_t)`.
pub fn shift_mle(x: &[F192], y: &[F192]) -> F192 {
    let n = x.len();
    let mut total = F192::ZERO;
    let mut low = F192::ONE; // Π_{t<j} x_t (1 + y_t)
    for j in 0..n {
        let mut high = F192::ONE;
        for t in j + 1..n {
            high *= F192::ONE + x[t] + y[t];
        }
        total += low * (F192::ONE + x[j]) * y[j] * high;
        low *= x[j] * (F192::ONE + y[j]);
    }
    total
}

/// `E'(ρ, x) = eq(ρ, x) + eq(ρ, 1⃗)·eq(1⃗, x)`: `eq(ρ, ·)` with row `2^n − 1` masked.
pub fn eq_masked(rho: &[F192], x: &[F192]) -> F192 {
    let ones = vec![F192::ONE; rho.len()];
    eq_eval(rho, x) + eq_eval(rho, &ones) * eq_eval(&ones, x)
}

/// The CH link's weights: `ω(l, p)` for `l < 8`, `W(m, q)` for the `Y` lanes `m < 4`, and the constant `C(ω)`.
pub struct ChWeights {
    pub omega: Vec<[F192; 64]>,
    pub w: Vec<[F192; 64]>,
    pub c: F192,
}

pub fn ch_weights(lam: &[F192], zeta: &[F192]) -> ChWeights {
    let (el, ez) = (eq_table(lam), eq_table(zeta));
    let omega: Vec<[F192; 64]> = (0..8).map(|l| std::array::from_fn(|p| el[l] * ez[p])).collect();
    let w: Vec<[F192; 64]> =
        (0..4).map(|m| std::array::from_fn(|q| if q <= 55 { omega[m][q + 8] } else { omega[m + 1][q - 56] })).collect();
    let mut c = omega[4][8];
    for p in 0..8 {
        if (0x43u64 >> p) & 1 == 1 {
            c += omega[0][p];
        }
    }
    ChWeights { omega, w, c }
}

/// The constant of `in` lane `l ≥ 5` (`Pad43`'s lanes 5–24).
pub fn pad43_const(l: usize) -> u64 {
    if l == 16 { 0x80u64 << 56 } else { 0 }
}

/// The 64 slices `Σ_k eqr[k]·bit_p(col[k])`, combined over columns with coefficients.
fn slices(cols: &[(&[F64], F192)], eqr: &[F192]) -> Vec<F192> {
    let mut out = vec![F192::ZERO; 64];
    for (col, coeff) in cols {
        let s = fold_1b_rows(col, eqr);
        for p in 0..64 {
            out[p] += *coeff * s[p];
        }
    }
    out
}

/// v1's ungated link (A9; the `CHlink` phase; claims `[ring in, ring Y]` then the 17 constant-lane word claims),
/// unused since S1; kept for tests.
#[allow(dead_code)]
pub fn prove_ch(ps: &mut ProverState, lay: &Layout, ch: &Chain, cmain: &[F64]) -> Vec<Claim> {
    prove_ch_gated(ps, lay, ch, cmain, None)
}

/// The sumcheck of [`sumcheck2`] when the kernels `t[0]`, `t[2]` vanish past `live` rows: every round touches the
/// live prefix only (P-GATE). Same messages and point as the dense one; returns the folded kernels `t[0](ρ')`,
/// `t[2](ρ')` (the partners' folds past `live` are not kept, so their values are not returned).
pub fn sumcheck2_live(ps: &mut ProverState, mut t: [Vec<F192>; 4], tail: [F192; 4], mut claim: F192, n_vars: usize) -> (Vec<F192>, F192, [F192; 2]) {
    // every table is constant (`tail`) past its stored prefix, and a fold keeps a constant tail; the kernels'
    // tails are zero, so pairs wholly in the tail add nothing, and a ragged pair takes its partner from the tail
    assert!(tail[0] == F192::ZERO && tail[2] == F192::ZERO);
    assert!(t.iter().all(|v| v.len() == t[0].len()), "the four stored prefixes have one length");
    let mut point = Vec::with_capacity(n_vars);
    for _ in 0..n_vars {
        let m = t[0].len().max(1);
        let m2 = m + (m & 1);
        for (v, &z) in t.iter_mut().zip(&tail) {
            v.resize(m2, z);
        }
        let (c0, c2) = round([&t[0], &t[1], &t[2], &t[3]]);
        let c1 = claim + c2;
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        for v in t.iter_mut() {
            fold(v, r);
        }
        point.push(r);
    }
    (point, claim, [t[0][0], t[2][0]])
}

/// S1 (BLUEPRINT2 §2.1; P-GATE): the CH link `in_{k+1} = Pad43(Y_k)` gated by `[k + 1 < n]` (i.e. `k + 1 ≤ m`), so the link leaves rows `≥ n` (zero inputs,
/// `Y = Z`) free; the GKR still binds `Y = Keccak-f(in)` there and the word claims force `in` lanes 8–24 to zero. `gate = Some((n, sparse))`: the kernels are `S_n(ρ, k) = eq(ρ, k − 1)·[k < n]`,
/// `E'_n(ρ, k) = eq(ρ, k)·[k < n − 1]`, target `C·Σ_{k < n−1} eq(ρ, k)`; the constant lanes' word claims are
/// `c_l · lt̃_n(ρ')`. `sparse` runs the rounds and the slices over the live prefix only, with the dead rows' `Y`
/// slices in closed form (`bits(Z)·(1 − lt̃_n(ρ'))`); it must give the dense gated prover's bytes.
/// The verifier's side: `lt̃_{n−1}(ρ)`, `lt̃_n(ρ')` and the gated kernels at `(ρ, ρ')`, closed forms in `n`
/// ([`lt_mle`], [`gated_kernel`]; Lean `LvmMask`).
pub fn prove_ch_gated(ps: &mut ProverState, lay: &Layout, ch: &Chain, cmain: &[F64], gate: Option<(usize, bool)>) -> Vec<Claim> {
    let ln = lay.log_n;
    let n = 1usize << ln;
    let chal = ps.sample_vec(ln + 3 + 6);
    let (rho, lam, zeta) = (&chal[..ln], &chal[ln..ln + 3], &chal[ln + 3..]);
    let wt = ch_weights(lam, zeta);
    let el = eq_table(lam);
    let tin: Vec<Vec<[F192; 256]>> = (0..8).map(|l| byte_tables(&wt.omega[l])).collect();
    let tw: Vec<Vec<[F192; 256]>> = (0..4).map(|m| byte_tables(&wt.w[m])).collect();
    let _ = el;
    if let Some((nl, sparse)) = gate {
        return prove_ch_gate_body(ps, lay, ch, cmain, nl, sparse, rho, lam, zeta, &wt, &tin, &tw);
    }
    let g: Vec<F192> = crate::lv::parallel::map_collect(n, |k| {
        let mut acc = F192::ZERO;
        for l in 0..8 {
            acc += bitdot(&tin[l], ch.inputs[k][l]);
        }
        acc
    });
    let hy: Vec<F192> = crate::lv::parallel::map_collect(n, |k| {
        let mut acc = F192::ZERO;
        for m in 0..4 {
            acc += bitdot(&tw[m], ch.y[k][m]);
        }
        acc
    });
    let eqr = eq_table(rho);
    let mut s = vec![F192::ZERO; n];
    s[1..].copy_from_slice(&eqr[..n - 1]);
    let mut em = eqr.clone();
    em[n - 1] = F192::ZERO;
    let ones = vec![F192::ONE; ln];
    let target = wt.c * (F192::ONE + eq_eval(rho, &ones));
    let (rho1, f1, _) = sumcheck2(ps, [s, g, em, hy], target);

    // the in slices at (ρ', λ, 0, 0, 0)
    let eq1 = eq_table(&rho1);
    let el = eq_table(lam);
    let in_cols: Vec<(&[F64], F192)> = (0..8).map(|l| (&cmain[lay.ch_slot(l)..][..n], el[l])).collect();
    let in_s = slices(&in_cols, &eq1);
    ps.add_scalars(&in_s);
    let in_point = [&rho1[..], lam, &[F192::ZERO; 3]].concat();
    let in_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());

    // the 2-round sumcheck over the Y lane bits m
    let ez = eq_table(zeta);
    let s_r = shift_mle(rho, &rho1);
    let mut t2 = f1;
    for p in 0..64 {
        t2 += s_r * ez[p] * in_s[p];
    }
    let em1 = eq_masked(rho, &rho1);
    let yhat: Vec<[F192; 64]> =
        (0..4).map(|m| fold_1b_rows(&cmain[lay.ch_y(m)..][..n], &eq1)).collect();
    // tables over m (4 entries) of 64-vectors: A_m = W(m, ·)·E', B_m = Ŷ(m, ·)
    let mut a: Vec<Vec<F192>> = (0..4).map(|m| wt.w[m].iter().map(|&x| em1 * x).collect()).collect();
    let mut b: Vec<Vec<F192>> = yhat.iter().map(|v| v.to_vec()).collect();
    let mut claim = t2;
    let mut mu = Vec::new();
    for _ in 0..2 {
        let half = a.len() / 2;
        let (mut c0, mut c2) = (F192::ZERO, F192::ZERO);
        for j in 0..half {
            for q in 0..64 {
                let (a0, a1, b0, b1) = (a[2 * j][q], a[2 * j + 1][q], b[2 * j][q], b[2 * j + 1][q]);
                c0 += a0 * b0;
                c2 += (a0 + a1) * (b0 + b1);
            }
        }
        let c1 = claim + c2;
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        let f = |v: &Vec<Vec<F192>>| -> Vec<Vec<F192>> {
            (0..half).map(|j| (0..64).map(|q| v[2 * j][q] + r * (v[2 * j][q] + v[2 * j + 1][q])).collect()).collect()
        };
        a = f(&a);
        b = f(&b);
        mu.push(r);
    }
    let y_s = b[0].clone();
    ps.add_scalars(&y_s);
    let y_point = [&rho1[..], &mu[..], &[F192::ONE, F192::ZERO, F192::ONE, F192::ONE]].concat();
    let y_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    let _const_lanes = ps.sample_vec(LANE_BITS);

    debug_assert!({
        let ok = claim == em1 * (0..64).map(|q| a[0][q] * y_s[q]).sum::<F192>();
        ok
    });
    let mut claims = vec![
        Claim::Ring { offset: lay.ch_off, point: in_point, slices: in_s, map: in_map },
        Claim::Ring { offset: lay.ch_off, point: y_point, slices: y_s, map: y_map },
    ];
    for l in 8..LANES {
        claims.push(Claim::point(lay.ch_slot(l), rho1.clone(), e(pad43_const(l))));
    }
    claims
}

#[allow(clippy::too_many_arguments)]
fn prove_ch_gate_body(
    ps: &mut ProverState, lay: &Layout, ch: &Chain, cmain: &[F64], nl: usize, sparse: bool, rho: &[F192], lam: &[F192],
    zeta: &[F192], wt: &ChWeights, tin: &[Vec<[F192; 256]>], tw: &[Vec<[F192; 256]>],
) -> Vec<Claim> {
    let ln = lay.log_n;
    let n = 1usize << ln;
    assert!(nl >= 1 && nl <= n);
    // rows the kernels can touch: k < nl
    let live = if sparse { nl } else { n };
    let g: Vec<F192> = crate::lv::parallel::map_collect(live, |k| {
        let mut acc = F192::ZERO;
        for l in 0..8 {
            acc += bitdot(&tin[l], ch.inputs.get(k).map_or(0, |x| x[l]));
        }
        acc
    });
    let hy: Vec<F192> = crate::lv::parallel::map_collect(live, |k| {
        let mut acc = F192::ZERO;
        for m in 0..4 {
            acc += bitdot(&tw[m], ch.y[k][m]);
        }
        acc
    });
    // eq(ρ, ·) on the live prefix only (sparse) or in full (dense)
    let eqr: Vec<F192> = if sparse { eq_prefix(rho, nl) } else { eq_table(rho) };
    let mut s = vec![F192::ZERO; live];
    let mut em = vec![F192::ZERO; live];
    for k in 0..nl.saturating_sub(1) {
        s[k + 1] = eqr[k];
        em[k] = eqr[k];
    }
    let below: F192 = eqr[..nl - 1].iter().copied().sum();
    let target = wt.c * below;
    let (rho1, f1, s_r, em1) = if sparse {
        let hz: F192 = (0..4).map(|m| bitdot(&tw[m], ch.y[n - 1][m])).sum();
        let tail = [F192::ZERO, F192::ZERO, F192::ZERO, if nl < n { hz } else { F192::ZERO }];
        let (r1, f1, [a, c]) = sumcheck2_live(ps, [s, g, em, hy], tail, target, ln);
        (r1, f1, a, c)
    } else {
        let (r1, f1, t) = sumcheck2(ps, [s, g, em, hy], target);
        (r1, f1, t[0], t[2])
    };

    // V's side (P-GATE check): the gated kernels and the thresholds in closed form, from n alone
    assert!(target == wt.c * lt_mle(rho, nl - 1), "target = C·lt̃_(n−1)(ρ)");
    assert!(s_r == gated_kernel(rho, &rho1, nl - 1, true), "S_n(ρ, ρ') in closed form");
    assert!(em1 == gated_kernel(rho, &rho1, nl - 1, false), "E'_n(ρ, ρ') in closed form");
    // the in slices at (ρ', λ, 0, 0, 0): dead rows are zero
    let eq1: Vec<F192> = if sparse { eq_prefix(&rho1, nl) } else { eq_table(&rho1) };
    let lt1: F192 = eq1[..nl].iter().copied().sum(); // lt̃_n(ρ')
    assert!(lt1 == lt_mle(&rho1, nl), "lt̃_n(ρ') in closed form");
    let el = eq_table(lam);
    let in_cols: Vec<(&[F64], F192)> = (0..8).map(|l| (&cmain[lay.ch_slot(l)..][..live], el[l])).collect();
    let in_s = slices(&in_cols, &eq1[..live]);
    ps.add_scalars(&in_s);
    let in_point = [&rho1[..], lam, &[F192::ZERO; 3]].concat();
    let in_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());

    let ez = eq_table(zeta);
    let mut t2 = f1;
    for p in 0..64 {
        t2 += s_r * ez[p] * in_s[p];
    }
    let yhat: Vec<[F192; 64]> = (0..4)
        .map(|m| {
            let mut v = fold_1b_rows(&cmain[lay.ch_y(m)..][..live], &eq1[..live]);
            if sparse && nl < n {
                // dead rows hold Z's lane m: its bits at weight 1 − lt̃_n(ρ')
                let zm = ch.y[n - 1][m];
                let dead = F192::ONE + lt1;
                for (q, v) in v.iter_mut().enumerate() {
                    if (zm >> q) & 1 == 1 {
                        *v += dead;
                    }
                }
            }
            v
        })
        .collect();
    let mut a: Vec<Vec<F192>> = (0..4).map(|m| wt.w[m].iter().map(|&x| em1 * x).collect()).collect();
    let mut b: Vec<Vec<F192>> = yhat.iter().map(|v| v.to_vec()).collect();
    let mut claim = t2;
    let mut mu = Vec::new();
    for _ in 0..2 {
        let half = a.len() / 2;
        let (mut c0, mut c2) = (F192::ZERO, F192::ZERO);
        for j in 0..half {
            for q in 0..64 {
                let (a0, a1, b0, b1) = (a[2 * j][q], a[2 * j + 1][q], b[2 * j][q], b[2 * j + 1][q]);
                c0 += a0 * b0;
                c2 += (a0 + a1) * (b0 + b1);
            }
        }
        let c1 = claim + c2;
        ps.add_round_poly(&[c0, c1, c2], false);
        let r = ps.sample();
        claim = c0 + r * (c1 + r * c2);
        let f = |v: &Vec<Vec<F192>>| -> Vec<Vec<F192>> {
            (0..half).map(|j| (0..64).map(|q| v[2 * j][q] + r * (v[2 * j][q] + v[2 * j + 1][q])).collect()).collect()
        };
        a = f(&a);
        b = f(&b);
        mu.push(r);
    }
    let y_s = b[0].clone();
    ps.add_scalars(&y_s);
    let y_point = [&rho1[..], &mu[..], &[F192::ONE, F192::ZERO, F192::ONE, F192::ONE]].concat();
    let y_map: [F192; RING_STAGES] = std::array::from_fn(|_| ps.sample());
    let _const_lanes = ps.sample_vec(LANE_BITS);
    debug_assert!(claim == em1 * (0..64).map(|q| a[0][q] * y_s[q]).sum::<F192>());
    let mut claims = vec![
        Claim::Ring { offset: lay.ch_off, point: in_point, slices: in_s, map: in_map },
        Claim::Ring { offset: lay.ch_off, point: y_point, slices: y_s, map: y_map },
    ];
    for l in 8..LANES {
        claims.push(Claim::point(lay.ch_slot(l), rho1.clone(), e(pad43_const(l)) * lt1));
    }
    claims
}

/// The verifier's closed forms for the gated link (P-GATE; what `V` and the circuit would evaluate):
/// `Σ_{k < m} eq(ρ, k)·eq(y, k + shift)` (with `k + 1 < 2^μ` when `shift`), a 6-state automaton over the bits,
/// low to high: state (carry of `+ shift`, comparison of `k`'s low bits with `m`'s). `O(μ)` products.
pub fn gated_kernel(rho: &[F192], y: &[F192], m: usize, shift: bool) -> F192 {
    // st[c][cmp]: cmp 0 = lt, 1 = eq, 2 = gt
    let mut st = [[F192::ZERO; 3]; 2];
    st[shift as usize][1] = F192::ONE;
    for t in 0..rho.len() {
        let mt = (m >> t) & 1;
        let mut nx = [[F192::ZERO; 3]; 2];
        for c in 0..2 {
            for cmp in 0..3 {
                let v = st[c][cmp];
                if v == F192::ZERO {
                    continue;
                }
                for kt in 0..2usize {
                    let wr = if kt == 1 { rho[t] } else { F192::ONE + rho[t] };
                    let ot = kt ^ c;
                    let wy = if ot == 1 { y[t] } else { F192::ONE + y[t] };
                    let nc = kt & c;
                    let ncmp = if kt < mt { 0 } else if kt > mt { 2 } else { cmp };
                    nx[nc][ncmp] += v * wr * wy;
                }
            }
        }
        st = nx;
    }
    st[0][0]
}

/// `lt̃_m(x) = Σ_{k < m} eq(x, k)`, `O(μ)`.
pub fn lt_mle(x: &[F192], m: usize) -> F192 {
    let mut total = F192::ZERO;
    let mut above = F192::ONE; // Π_{s > t} eq(x_s, m_s)
    for t in (0..x.len()).rev() {
        if (m >> t) & 1 == 1 {
            total += above * (F192::ONE + x[t]);
            above *= x[t];
        } else {
            above *= F192::ONE + x[t];
        }
    }
    if m >> x.len() != 0 { F192::ONE } else { total }
}

/// `eq(r, k)` for `k < len` only: the tensor's prefix, at `O(len + log)` products.
pub fn eq_prefix(r: &[F192], len: usize) -> Vec<F192> {
    // high variables first: the prefix of length `len` is a union of aligned blocks
    let nv = r.len();
    let mut out = vec![F192::ZERO; len];
    let mut k = 0usize;
    while k < len {
        // the largest aligned block at k that fits
        let mut b = if k == 0 { nv } else { (k.trailing_zeros() as usize).min(nv) };
        while (1usize << b) > len - k {
            b -= 1;
        }
        // eq(r, k + j) = eq(r_high, k >> b) · eq(r_low, j)
        let mut hi = F192::ONE;
        for t in b..nv {
            hi *= if (k >> t) & 1 == 1 { r[t] } else { F192::ONE + r[t] };
        }
        let lo = eq_table(&r[..b]);
        for (j, x) in lo.iter().enumerate() {
            out[k + j] = hi * *x;
        }
        k += 1 << b;
    }
    out
}

/// The KS sponge link's structured kernel table `Sc(ρ, k) = eq(ρ, k + 1)·cont_{k+1}`.
pub fn ks_kernel(eqr: &[F192], cont: &[bool]) -> Vec<F192> {
    let n = eqr.len();
    (0..n).map(|k| if k + 1 < n && cont[k + 1] { eqr[k + 1] } else { F192::ZERO }).collect()
}

/// Prove the KS link (the `KSlink` phase). Returns `[Y^ω, in^ω, M^ω, X^ω]` claims (Lean order).
pub fn prove_ks(ps: &mut ProverState, lay: &Layout, ks: &Sponge) -> Vec<Claim> {
    let kl = lay.ks_log;
    let n = 1usize << kl;
    let chal = ps.sample_vec(kl + LANE_BITS);
    let (rho, lam) = (&chal[..kl], &chal[kl..]);
    let om = eq_table(lam);
    let eqr = eq_table(rho);
    let sc = ks_kernel(&eqr, &ks.cont);
    let comb = |w: &[u64]| -> F192 { w.iter().zip(&om).map(|(&x, &o)| o.mul_base(F64(x))).sum() };
    let yw: Vec<F192> = crate::lv::parallel::map_collect(n, |k| comb(&ks.outputs[k]));
    let rest: Vec<F192> = crate::lv::parallel::map_collect(n, |k| comb(&ks.inputs[k]) + comb(&ks.msg[k]));
    let (rho1, _f, _) = sumcheck2(ps, [sc, yw, eqr, rest], F192::ZERO);
    let eq1 = eq_table(&rho1);
    let at = |f: &(dyn Fn(usize) -> F192 + Sync)| -> F192 {
        crate::lv::parallel::fold_reduce(n, || F192::ZERO, |acc, k| *acc += eq1[k] * f(k), |a, b| a + b)
    };
    let y = at(&|k| comb(&ks.outputs[k]));
    let inw = at(&|k| comb(&ks.inputs[k]));
    let lo = &rho1[..lay.rec_log];
    let eqlo = eq_table(lo);
    let half = 1usize << lay.rec_log;
    let mw: F192 = (0..half).map(|i| eqlo[i] * comb(&ks.msg[i])).sum();
    let xw: F192 = (0..half).map(|i| eqlo[i] * comb(&ks.msg[half + i])).sum();
    ps.add_scalars(&[y, inw, mw, xw]);
    let y_terms = (0..LANES).map(|l| (lay.ks_y(l), rho1.clone(), om[l])).collect();
    let in_terms = (0..LANES).map(|l| (lay.ks_slot(l), rho1.clone(), om[l])).collect();
    let m_terms = (0..REC_STREAM_COLS).map(|l| (lay.rec_col(l), lo.to_vec(), om[l])).collect();
    let x_terms = (0..REC_STREAM_COLS).map(|l| (lay.x(l), lo.to_vec(), om[l])).collect();
    vec![
        Claim::Point { terms: y_terms, value: y },
        Claim::Point { terms: in_terms, value: inw },
        Claim::Point { terms: m_terms, value: mw },
        Claim::Point { terms: x_terms, value: xw },
    ]
}
