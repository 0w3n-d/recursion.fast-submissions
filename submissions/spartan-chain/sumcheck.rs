//! Honest sumcheck provers (BLUEPRINT-R1 §3, §4.4). Every sumcheck binds variable 0 first; a
//! round polynomial is its coefficients, ascending (degree 3 for the outer sumcheck, 2 for the
//! others). The round polynomial is the unique one of the definition, so any correct way of
//! computing it gives the same bytes; the code below avoids materialising `E` tables over the
//! full cube in the first three rounds by reading the bit tables through lookup tables of
//! `Σ_{b<2^l} p_b eq(r_{<l}, b)` over bit patterns `p` (the "small-value" rounds).

use crate::chain::{pub_bit, row_factors, Shape, Witness};
use crate::circuit::{Circuit, BLOCK, CPOS};
use crate::field::{ETab, E};
use crate::mle::{coeffs2, eq_table, horner};
use crate::par;
use crate::transcript::Transcript;

pub const KIND_OUTER: u8 = 0x03;
pub const KIND_INNER: u8 = 0x05;
pub const KIND_RS: u8 = 0x07;

pub fn bytes_of(es: &[E]) -> Vec<u8> {
    let mut v = Vec::with_capacity(24 * es.len());
    for e in es {
        v.extend_from_slice(&e.to_bytes());
    }
    v
}

/// `T[p] = Σ_{b : bit b of p} eqr[b]` for every pattern `p` of `eqr.len()` bits.
fn pattern_table(eqr: &[E]) -> Vec<E> {
    let w = eqr.len();
    let mut t = vec![E::ZERO; 1 << w];
    for p in 1..(1usize << w) {
        let low = p.trailing_zeros() as usize;
        t[p] = t[p & (p - 1)] + eqr[low];
    }
    t
}

#[inline(always)]
fn chunk_bits(v: &[u64], off: usize, width: usize) -> usize {
    // width ≤ 16 and aligned: the chunk lies in one word
    ((v[off >> 6] >> (off & 63)) as usize) & ((1usize << width) - 1)
}

fn fold(v: &[E], r: E) -> Vec<E> {
    let half = v.len() / 2;
    if half >= 1 << 14 {
        let tab = ETab::new(r);
        return par::collect_vec(half, 1 << 12, |i| {
            let a = v[2 * i];
            a + tab.mul(a + v[2 * i + 1])
        });
    }
    let mut out = vec![E::ZERO; half];
    {
        for i in 0..half {
            let a = v[2 * i];
            out[i] = a + r * (a + v[2 * i + 1]);
        }
    }
    out
}

/// Split `eq(τ_{vars}, ·)` into a low table (≤ 12 variables) and a high table.
fn eq_split(vars: &[E]) -> (Vec<E>, Vec<E>, usize) {
    let hb = vars.len().min(12);
    (eq_table(&vars[..hb]), eq_table(&vars[hb..]), hb)
}

pub struct OuterOut {
    pub polys: Vec<[E; 4]>,
    pub r_x: Vec<E>,
    pub v: [E; 3],
}

/// The outer sumcheck: `0 = Σ_x eq(τ, x)·((Az)(x)(Bz)(x) + (Cz)(x))`, `ℓ_x` rounds, degree 3.
pub fn outer(sh: &Shape, wit: &Witness, tau: &[E], tr: &mut Transcript) -> OuterOut {
    let ell = sh.ell;
    let mut r: Vec<E> = vec![];
    let mut polys = vec![];
    let mut claim = E::ZERO;
    let mut prefix = E::ONE;
    let mut tabs: Option<[Vec<E>; 3]> = None;
    let verbose = std::env::var("SPARTAN_VERBOSE").map(|v| v == "2").unwrap_or(false);
    for l in 0..ell {
        let tl = std::time::Instant::now();
        let rem = ell - l - 1;
        let (eq_lo, eq_hi, hb) = eq_split(&tau[l + 1..]);
        let nhi = 1usize << (rem - hb);
        let parts: Vec<[E; 3]> = if l < 3 {
            // pattern rounds on the bit tables, bucketed by pattern
            let pw = 1usize << l;
            let t = pattern_table(&eq_table(&r[..l]));
            let np = 1usize << pw;
            let mut pt = vec![E::ZERO; np * np];
            for pa in 0..np {
                for pb in 0..np {
                    pt[pa * np + pb] = t[pa] * t[pb];
                }
            }
            let (ta, tb, tc) = (&wit.a, &wit.b, &wit.c);
            let (t, pt, eq_lo, eq_hi) = (&t, &pt, &eq_lo, &eq_hi);
            par::map_chunks(nhi, 1, |h0, h1| {
                let mut tot = [E::ZERO; 3];
                let mut ab = vec![[E::ZERO; 3]; np * np];
                let mut cb = vec![[E::ZERO; 2]; np];
                for hi in h0..h1 {
                    for x in ab.iter_mut() {
                        *x = [E::ZERO; 3];
                    }
                    for x in cb.iter_mut() {
                        *x = [E::ZERO; 2];
                    }
                    for lo in 0..(1usize << hb) {
                        let y = lo + (hi << hb);
                        let off = y << (l + 1);
                        let ca = chunk_bits(ta, off, 2 * pw);
                        let cbb = chunk_bits(tb, off, 2 * pw);
                        let cc = chunk_bits(tc, off, 2 * pw);
                        let m = np - 1;
                        let (a0, a1) = (ca & m, ca >> pw);
                        let (b0, b1) = (cbb & m, cbb >> pw);
                        let (c0, c1) = (cc & m, cc >> pw);
                        let e = eq_lo[lo];
                        ab[a0 * np + b0][0] += e;
                        ab[a1 * np + b1][1] += e;
                        ab[(a0 ^ a1) * np + (b0 ^ b1)][2] += e;
                        cb[c0][0] += e; // C is linear in X: no leading term
                        cb[c1][1] += e;
                    }
                    let mut s = [E::ZERO; 3];
                    for key in 0..np * np {
                        if pt[key].is_zero() {
                            continue;
                        }
                        for c in 0..3 {
                            if !ab[key][c].is_zero() {
                                s[c] += ab[key][c] * pt[key];
                            }
                        }
                    }
                    for key in 1..np {
                        for c in 0..2 {
                            if !cb[key][c].is_zero() {
                                s[c] += cb[key][c] * t[key];
                            }
                        }
                    }
                    for c in 0..3 {
                        tot[c] += eq_hi[hi] * s[c];
                    }
                }
                tot
            })
        } else if l == 3 {
            // the fourth round on the bit tables: byte patterns, values by lookup
            let t = pattern_table(&eq_table(&r[..3]));
            let pt = par::collect_vec(256 * 256, 1 << 10, |key| t[key >> 8] * t[key & 255]);
            let (ta, tb, tc) = (&wit.a, &wit.b, &wit.c);
            let (t, pt, eq_lo, eq_hi) = (&t, &pt, &eq_lo, &eq_hi);
            par::map_chunks(nhi, 1, |h0, h1| {
                let mut tot = [E::ZERO; 3];
                for hi in h0..h1 {
                    let mut s = [E::ZERO; 3];
                    for lo in 0..(1usize << hb) {
                        let y = lo + (hi << hb);
                        let off = y << 4;
                        let ca = chunk_bits(ta, off, 16);
                        let cbb = chunk_bits(tb, off, 16);
                        let cc = chunk_bits(tc, off, 16);
                        let (a0, a1) = (ca & 255, ca >> 8);
                        let (b0, b1) = (cbb & 255, cbb >> 8);
                        let (c0, c1) = (cc & 255, cc >> 8);
                        let e = eq_lo[lo];
                        s[0] += e * (pt[(a0 << 8) | b0] + t[c0]);
                        s[1] += e * (pt[(a1 << 8) | b1] + t[c1]);
                        s[2] += e * pt[((a0 ^ a1) << 8) | (b0 ^ b1)];
                    }
                    for c in 0..3 {
                        tot[c] += eq_hi[hi] * s[c];
                    }
                }
                tot
            })
        } else {
            let [ta, tb, tc] = tabs.as_ref().unwrap();
            let (eq_lo, eq_hi) = (&eq_lo, &eq_hi);
            par::map_chunks(nhi, 1, |h0, h1| {
                let mut tot = [E::ZERO; 3];
                for hi in h0..h1 {
                    let mut s = [E::ZERO; 3];
                    for lo in 0..(1usize << hb) {
                        let y = lo + (hi << hb);
                        let (a0, a1) = (ta[2 * y], ta[2 * y + 1]);
                        let (b0, b1) = (tb[2 * y], tb[2 * y + 1]);
                        let (c0, c1) = (tc[2 * y], tc[2 * y + 1]);
                        let e = eq_lo[lo];
                        s[0] += e * (a0 * b0 + c0);
                        s[1] += e * (a1 * b1 + c1);
                        s[2] += e * ((a0 + a1) * (b0 + b1));
                    }
                    for c in 0..3 {
                        tot[c] += eq_hi[hi] * s[c];
                    }
                }
                tot
            })
        };
        let mut hv = [E::ZERO; 3];
        for p in parts {
            for c in 0..3 {
                hv[c] += p[c];
            }
        }
        let [h0, h1, h2] = coeffs2(hv[0], hv[1], hv[2]);
        let a = E::ONE + tau[l];
        let g = [prefix * a * h0, prefix * (a * h1 + h0), prefix * (a * h2 + h1), prefix * h2];
        debug_assert_eq!(g[1] + g[2] + g[3], claim, "outer round {l}");
        tr.absorb(KIND_OUTER, &bytes_of(&g));
        let rl = tr.squeeze_e();
        claim = horner(&g, rl);
        prefix *= E::ONE + tau[l] + rl;
        r.push(rl);
        polys.push(g);
        if l == 3 {
            // materialise the three tables with four variables bound: 16-bit pattern ↦ T_4
            let t4 = pattern_table(&eq_table(&r[..4]));
            let mk = |bits: &Vec<u64>| -> Vec<E> {
                par::collect_vec(1usize << (ell - 4), 1 << 14, |y| {
                    t4[((bits[y >> 2] >> (16 * (y & 3))) & 0xFFFF) as usize]
                })
            };
            tabs = Some([mk(&wit.a), mk(&wit.b), mk(&wit.c)]);
        } else if l > 3 {
            let [ta, tb, tc] = tabs.take().unwrap();
            tabs = Some([fold(&ta, rl), fold(&tb, rl), fold(&tc, rl)]);
        }
        if verbose {
            eprintln!("  outer round {l}: {:.3}s", tl.elapsed().as_secs_f64());
        }
    }
    let [ta, tb, tc] = tabs.unwrap();
    OuterOut { polys, r_x: r, v: [ta[0], tb[0], tc[0]] }
}

pub struct InnerOut {
    pub polys: Vec<[E; 3]>,
    pub r_y: Vec<E>,
    pub final_m: E,
    pub final_z: E,
}

/// The inner sumcheck: `v_A + ρ v_B + ρ² v_C = Σ_y M̃ρ(r_x, y)·z(y)`, `ℓ_y` rounds, degree 2.
///
/// On `top = 0` the table is a sum of three tensors `Σ_i P_i(j)·γ_i(t')` (region 0 through the
/// transpose walk; the wiring and tail rows through `eq(r_kj, ·)` on the output and message
/// ranges); on `top = 1` it is supported on `t' = 0`, `j < 513` (`Mpub`). The first 14 rounds
/// bind `j`; the last `κ + 1` run on a dense table over `(t', top)`.
pub fn inner(
    circ: &Circuit,
    sh: &Shape,
    wit: &Witness,
    s: &[u8; 32],
    r_x: &[E],
    rho: E,
    claim0: E,
    tr: &mut Transcript,
) -> InnerOut {
    let kp = sh.kappa;
    let nb = sh.blocks();
    let rf = row_factors(sh, r_x);
    let rho2 = rho * rho;
    // P_0 = U = uA + ρ uB + ρ² e (C = I)
    let eb: Vec<E> = rf.e.iter().map(|&x| x * rho).collect();
    let mut p0 = circ.transpose(&rf.e, &eb);
    for j in 0..BLOCK {
        p0[j] += rho2 * rf.e[j];
    }
    let mut p1 = vec![E::ZERO; BLOCK];
    let mut p2 = vec![E::ZERO; BLOCK];
    for j in 0..256 {
        p1[256 + j] = rf.ekj[j];
        p2[648 + j] = rf.ekj[j];
    }
    let eq_t = eq_table(&r_x[14..14 + kp]);
    let eq_t2 = eq_table(&r_x[8..8 + kp]);
    let mut gam = [vec![E::ZERO; nb], vec![E::ZERO; nb], vec![E::ZERO; nb]];
    for t in 0..nb {
        gam[0][t] = rf.r0 * eq_t[t];
        let mut g1 = if t + 1 < nb { eq_t2[t + 1] * rf.rw } else { E::ZERO };
        if t as u64 == sh.n - 1 {
            g1 += rf.rt;
        }
        gam[1][t] = g1;
        gam[2][t] = rho2 * eq_t2[t] * rf.rw;
    }
    let mut mpub = vec![E::ZERO; BLOCK];
    mpub[0] = rf.e[CPOS] * rf.r0 * (E::ONE + rho) + rho * (rf.rw + rf.rt);
    for j in 0..256 {
        mpub[1 + j] = rf.ekj[j] * rf.t0 * rf.rw;
        mpub[257 + j] = rho2 * rf.ekj[j] * rf.rt;
    }
    let mut zpub: Vec<E> = (0..BLOCK).map(|u| E::from_bit(pub_bit(s, &wit.h, u))).collect();
    let mut ps = [p0, p1, p2];
    let mut ranges = [(0usize, BLOCK), (256, 512), (648, 904)];

    let mut r: Vec<E> = vec![];
    let mut polys = vec![];
    let mut claim = claim0;
    let mut zt: Vec<E> = vec![];
    for l in 0..14 {
        let half = BLOCK >> (l + 1); // pairs j''' per block
        let parts: Vec<[E; 3]> = if l < 3 {
            let pw = 1usize << l;
            let np = 1usize << pw;
            let t = pattern_table(&eq_table(&r[..l]));
            let (t, ps, ranges, gam, w) = (&t, &ps, &ranges, &gam, &wit.w);
            par::map_chunks(nb, 1, |t0, t1| {
                let mut tot = [E::ZERO; 3];
                let mut bk = vec![[E::ZERO; 3]; np];
                for tp in t0..t1 {
                    for i in 0..3 {
                        for x in bk.iter_mut() {
                            *x = [E::ZERO; 3];
                        }
                        let p = &ps[i];
                        let (lo, hi) = ranges[i];
                        for jj in (lo >> 1)..((hi + 1) >> 1).min(half) {
                            let (pa, pb) = (p[2 * jj], p[2 * jj + 1]);
                            let ch = chunk_bits(w, BLOCK * tp + (jj << (l + 1)), 2 * pw);
                            let (z0, z1) = (ch & (np - 1), ch >> pw);
                            bk[z0][0] += pa;
                            bk[z1][1] += pb;
                            bk[z0 ^ z1][2] += pa + pb;
                        }
                        let mut sv = [E::ZERO; 3];
                        for key in 1..np {
                            for c in 0..3 {
                                if !bk[key][c].is_zero() {
                                    sv[c] += bk[key][c] * t[key];
                                }
                            }
                        }
                        for c in 0..3 {
                            tot[c] += gam[i][tp] * sv[c];
                        }
                    }
                }
                tot
            })
        } else {
            let (ps, ranges, gam, zt) = (&ps, &ranges, &gam, &zt);
            let blk = BLOCK >> l; // entries per t' in zt
            par::map_chunks(nb, 1, |t0, t1| {
                let mut tot = [E::ZERO; 3];
                for tp in t0..t1 {
                    let z = &zt[blk * tp..blk * (tp + 1)];
                    for i in 0..3 {
                        let p = &ps[i];
                        let (lo, hi) = ranges[i];
                        let mut sv = [E::ZERO; 3];
                        for jj in (lo >> 1)..((hi + 1) >> 1).min(half) {
                            let (pa, pb) = (p[2 * jj], p[2 * jj + 1]);
                            let (za, zb) = (z[2 * jj], z[2 * jj + 1]);
                            sv[0] += pa * za;
                            sv[1] += pb * zb;
                            sv[2] += (pa + pb) * (za + zb);
                        }
                        for c in 0..3 {
                            tot[c] += gam[i][tp] * sv[c];
                        }
                    }
                }
                tot
            })
        };
        let mut gv = [E::ZERO; 3];
        for p in parts {
            for c in 0..3 {
                gv[c] += p[c];
            }
        }
        // the public half (t' = 0, top = 1)
        for jj in 0..half {
            let (ma, mb) = (mpub[2 * jj], mpub[2 * jj + 1]);
            let (za, zb) = (zpub[2 * jj], zpub[2 * jj + 1]);
            gv[0] += ma * za;
            gv[1] += mb * zb;
            gv[2] += (ma + mb) * (za + zb);
        }
        let g = coeffs2(gv[0], gv[1], gv[2]);
        debug_assert_eq!(g[1] + g[2], claim, "inner round {l}");
        tr.absorb(KIND_INNER, &bytes_of(&g));
        let rl = tr.squeeze_e();
        claim = horner(&g, rl);
        r.push(rl);
        polys.push(g);
        for i in 0..3 {
            ps[i] = fold(&ps[i], rl);
            ranges[i] = (ranges[i].0 >> 1, (ranges[i].1 + 1) >> 1);
        }
        mpub = fold(&mpub, rl);
        zpub = fold(&zpub, rl);
        if l == 2 {
            let t3 = pattern_table(&eq_table(&r[..3]));
            let w = &wit.w;
            zt = par::collect_vec(1usize << (sh.lw - 3), 1 << 14, |y| t3[((w[y >> 3] >> (8 * (y & 7))) & 255) as usize]);
        } else if l > 2 {
            zt = fold(&zt, rl);
        }
    }
    // phase 2: dense tables over (t', top)
    let sz = 2 * nb;
    let mut m2 = vec![E::ZERO; sz];
    let mut z2 = vec![E::ZERO; sz];
    for t in 0..nb {
        m2[t] = ps[0][0] * gam[0][t] + ps[1][0] * gam[1][t] + ps[2][0] * gam[2][t];
        z2[t] = zt[t];
    }
    m2[nb] = mpub[0];
    z2[nb] = zpub[0];
    let (p2polys, r2, fm, fz) = product_sumcheck(m2, z2, claim, KIND_INNER, tr);
    polys.extend(p2polys);
    r.extend(r2);
    InnerOut { polys, r_y: r, final_m: fm, final_z: fz }
}

/// A degree-2 sumcheck of `Σ_y f(y) g(y)` over dense tables. Returns the round polynomials, the
/// challenges and the final `f`, `g` values.
pub fn product_sumcheck(
    f: Vec<E>,
    g: Vec<E>,
    claim: E,
    kind: u8,
    tr: &mut Transcript,
) -> (Vec<[E; 3]>, Vec<E>, E, E) {
    product_rounds(f, g, claim, &mut |poly: &[E; 3]| {
        tr.absorb(kind, &bytes_of(poly));
        tr.squeeze_e()
    })
}

/// The rounds of `product_sumcheck` with the challenges from `next` (given each polynomial).
pub fn product_rounds(
    mut f: Vec<E>,
    mut g: Vec<E>,
    mut claim: E,
    next: &mut dyn FnMut(&[E; 3]) -> E,
) -> (Vec<[E; 3]>, Vec<E>, E, E) {
    let mut polys = vec![];
    let mut r = vec![];
    while f.len() > 1 {
        let half = f.len() / 2;
        let (fr, gr) = (&f, &g);
        let parts = par::map_chunks(half, 1 << 12, |a, b| {
            let mut s = [E::ZERO; 3];
            for y in a..b {
                let (f0, f1, g0, g1) = (fr[2 * y], fr[2 * y + 1], gr[2 * y], gr[2 * y + 1]);
                s[0] += f0 * g0;
                s[1] += f1 * g1;
                s[2] += (f0 + f1) * (g0 + g1);
            }
            s
        });
        let mut sv = [E::ZERO; 3];
        for p in parts {
            for c in 0..3 {
                sv[c] += p[c];
            }
        }
        let poly = coeffs2(sv[0], sv[1], sv[2]);
        debug_assert_eq!(poly[1] + poly[2], claim);
        let rl = next(&poly);
        claim = horner(&poly, rl);
        f = fold(&f, rl);
        g = fold(&g, rl);
        polys.push(poly);
        r.push(rl);
    }
    debug_assert_eq!(f[0] * g[0], claim);
    (polys, r, f[0], g[0])
}

/// The 64 slices `s_i = Q̃_i(r_hi)`, `Q_i(u') = bit i of q(u')` (§4.2).
pub fn slices(q: &[u64], eq_hi: &[E]) -> Vec<E> {
    let parts = par::map_chunks(q.len(), 1 << 12, |a, b| {
        let mut acc = [E::ZERO; 64];
        for u in a..b {
            let mut word = q[u];
            let e = eq_hi[u];
            while word != 0 {
                let i = word.trailing_zeros() as usize;
                acc[i] += e;
                word &= word - 1;
            }
        }
        acc
    });
    let mut s = vec![E::ZERO; 64];
    for p in parts {
        for i in 0..64 {
            s[i] += p[i];
        }
    }
    s
}
