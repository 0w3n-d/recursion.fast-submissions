//! Multilinear helpers (BLUEPRINT-R1 notation): `eq(r, u) = ∏_l (1 + r_l + u_l)`, `u_0` the least
//! significant bit of the index.

use crate::field::{ETab, E};
use crate::par;

/// `eq(r, ·)` over `{0,1}^ℓ`, index bit `l` ↔ `r[l]`.
pub fn eq_table(r: &[E]) -> Vec<E> {
    let mut t = Vec::with_capacity(1usize << r.len());
    t.push(E::ONE);
    for &rl in r {
        let n = t.len();
        t.resize(2 * n, E::ZERO);
        let big = n >= 1 << 12;
        let tab = if big { Some(ETab::new(rl)) } else { None };
        // t[u + n] = t[u]·r_l, t[u] = t[u]·(1 + r_l) = t[u] + t[u + n]
        let (lo, hi) = t.split_at_mut(n);
        let work = |off: usize, chunk: &mut [E]| {
            for (i, h) in chunk.iter_mut().enumerate() {
                let a = lo[off + i];
                *h = match &tab {
                    Some(tb) => tb.mul(a),
                    None => a * rl,
                };
            }
        };
        if big {
            par::for_each_chunk_mut(hi, 1 << 12, work);
        } else {
            work(0, hi);
        }
        for i in 0..n {
            let h = hi[i];
            lo[i] += h;
        }
    }
    t
}

/// `eq(r, u)` for the integer `u` (bits beyond `r.len()` must be zero).
pub fn eq_at(r: &[E], u: u64) -> E {
    let mut acc = E::ONE;
    for (l, &rl) in r.iter().enumerate() {
        acc *= if (u >> l) & 1 == 1 { rl } else { rl + E::ONE };
    }
    acc
}

/// `eq(a, b) = ∏_l (1 + a_l + b_l)`.
pub fn eq_ee(a: &[E], b: &[E]) -> E {
    assert_eq!(a.len(), b.len());
    let mut acc = E::ONE;
    for i in 0..a.len() {
        acc *= E::ONE + a[i] + b[i];
    }
    acc
}

/// `Σ_u t[u]·eq(r, u)` — the multilinear extension of a table at `r` (tests and KAT only).
pub fn mle_eval(t: &[E], r: &[E]) -> E {
    assert_eq!(t.len(), 1 << r.len());
    let eq = eq_table(r);
    let mut acc = E::ZERO;
    for i in 0..t.len() {
        acc += t[i] * eq[i];
    }
    acc
}

/// Horner evaluation of a polynomial given by ascending coefficients.
pub fn horner(c: &[E], x: E) -> E {
    let mut acc = E::ZERO;
    for &ci in c.iter().rev() {
        acc = acc * x + ci;
    }
    acc
}

/// The coefficients of a degree-2 polynomial from `g(0)`, `g(1)` and the leading coefficient
/// `g(∞)`: `c0 = g(0)`, `c2 = g(∞)`, `c1 = g(1) + c0 + c2`.
pub fn coeffs2(g0: E, g1: E, ginf: E) -> [E; 3] {
    [g0, g1 + g0 + ginf, ginf]
}
