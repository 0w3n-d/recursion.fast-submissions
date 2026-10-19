//! `proveLeaf` (BLUEPRINT-R1 §1.4): the honest leaf proof, byte for byte as §7, under the oracle
//! `blake2sOracle`. The protocol is deterministic given the oracle.

use std::time::Instant;

use crate::blake2s::{chain_end, Digest};
use crate::chain::{leaf_size, witness, Shape, T_COLS};
use crate::circuit::Circuit;
use crate::field::{E, K};
use crate::mle::eq_table;
use crate::par;
use crate::ringswitch::{target, PhiTab, STAGES};
use crate::rs::Code;
use crate::sumcheck::{bytes_of, inner, outer, product_sumcheck, slices, KIND_RS};
use crate::transcript::{leaf_label, Label, Merkle, Transcript};

pub struct Timings(pub Vec<(&'static str, f64)>);

impl Timings {
    pub fn report(&self) -> String {
        self.0.iter().map(|(k, v)| format!("{k}={v:.3}s")).collect::<Vec<_>>().join(" ")
    }
}

/// The 80-byte leaf header `enc64 0 ‖ s ‖ enc64 n ‖ h`.
pub fn leaf_header(s: &Digest, n: u64, h: &Digest) -> Vec<u8> {
    let mut out = Vec::with_capacity(leaf_size(n));
    out.extend_from_slice(&0u64.to_le_bytes());
    out.extend_from_slice(s);
    out.extend_from_slice(&n.to_le_bytes());
    out.extend_from_slice(h);
    out
}

/// `Σ_i c_i Q[i]` for `c ∈ E^m`, `Q` the `m × k` matrix of words.
fn combine_rows(q: &[u64], m: usize, k: usize, c: &[E]) -> Vec<E> {
    par::collect_vec(k, 1 << 10, |j| {
        let mut acc = E::ZERO;
        for i in 0..m {
            acc += c[i].mul_k(K(q[i * k + j]));
        }
        acc
    })
}

/// The honest leaf proof for `(s, n)`, and the timings of its phases. With `log`, the
/// transcript's state sequence is returned too.
/// The challenges and tables of one leaf proof (the known-answer harness, `kat.rs`).
#[derive(Default)]
pub struct LeafTrace {
    pub tau: Vec<E>,
    pub r_x: Vec<E>,
    pub rho: E,
    pub r_y: Vec<E>,
    pub f: Vec<E>,
    pub r2: Vec<E>,
    pub w: Vec<u64>,
    pub a: Vec<u64>,
    pub b: Vec<u64>,
    pub c: Vec<u64>,
    pub h: Digest,
}

pub fn prove_leaf(
    circ: &Circuit,
    s: &Digest,
    n: u64,
    log: bool,
) -> (Vec<u8>, Timings, Option<Vec<(String, Digest)>>) {
    prove_leaf_traced(circ, s, n, log, None)
}

pub fn prove_leaf_traced(
    circ: &Circuit,
    s: &Digest,
    n: u64,
    log: bool,
    trace: Option<&mut LeafTrace>,
) -> (Vec<u8>, Timings, Option<Vec<(String, Digest)>>) {
    let mut tm = vec![];
    if n == 0 {
        return (leaf_header(s, 0, s), Timings(tm), None);
    }
    let t0 = Instant::now();
    let mut lap = |name: &'static str, t: &mut Instant| {
        tm.push((name, t.elapsed().as_secs_f64()));
        *t = Instant::now();
    };
    let mut t = Instant::now();
    let sh = Shape::new(n);
    let wit = witness(circ, &sh, s);
    debug_assert_eq!(wit.h, chain_end(s, n));
    debug_assert!(crate::chain::sat_tables(&wit));
    lap("witness", &mut t);

    // Ligero commitment (§5.3): rows Q[i] = q(j + k i), encoded over K
    let (m, k, nn, ln) = (sh.m, sh.k, sh.nn, sh.ln);
    let q = &wit.w;
    let code = Code::new(sh.lk, ln);
    let mut u: Vec<Vec<K>> = vec![vec![]; m];
    par::for_each_chunk_mut(&mut u, 1, |off, rows| {
        for (i, row) in rows.iter_mut().enumerate() {
            let msg: Vec<K> = q[(off + i) * k..(off + i + 1) * k].iter().map(|&x| K(x)).collect();
            *row = code.encode_k(&msg);
        }
    });
    lap("encode", &mut t);
    let col_bytes = |c: usize| -> Vec<u8> {
        let mut b = Vec::with_capacity(8 * m);
        for row in u.iter() {
            b.extend_from_slice(&row[c].to_bytes());
        }
        b
    };
    let mut leaves: Vec<Label> = vec![[0u8; 31]; nn];
    par::fill(&mut leaves, 1 << 8, |c| leaf_label(&col_bytes(c)));
    let tree = Merkle::build(leaves);
    let root = tree.root();
    lap("merkle", &mut t);

    let mut tr = Transcript::new(s, n, &wit.h, log);
    tr.absorb(0x01, &root);
    let rcoef: Vec<E> = (0..m).map(|_| tr.squeeze_e()).collect();
    let ubar = combine_rows(q, m, k, &rcoef);
    tr.absorb(0x02, &bytes_of(&ubar));
    let tau: Vec<E> = (0..sh.ell).map(|_| tr.squeeze_e()).collect();
    lap("proximity", &mut t);

    let out = outer(&sh, &wit, &tau, &mut tr);
    lap("outer", &mut t);
    let [va, vb, vc] = out.v;
    tr.absorb(0x04, &bytes_of(&out.v));
    let rho = tr.squeeze_e();
    let inn = inner(circ, &sh, &wit, s, &out.r_x, rho, va + rho * vb + rho * rho * vc, &mut tr);
    lap("inner", &mut t);

    // slices and ring switching (§4)
    let r_y = &inn.r_y;
    let r_lo = &r_y[..6];
    let r_hi = &r_y[6..sh.lw];
    let eq_hi = eq_table(r_hi);
    let sl = slices(q, &eq_hi);
    debug_assert_eq!(
        {
            // z̃(r_y) = (1 + r_ytop) w̃(r_u) + r_ytop pub̃(r_u), w̃(r_u) = Σ_i eq(r_lo, i) s_i
            let el = eq_table(r_lo);
            let wt = (0..64).fold(E::ZERO, |a, i| a + el[i] * sl[i]);
            let ytop = r_y[sh.lw];
            (E::ONE + ytop) * wt + ytop * crate::chain::pub_mle(s, &wit.h, &r_y[..sh.lw])
        },
        inn.final_z,
        "slices"
    );
    tr.absorb(0x06, &bytes_of(&sl));
    let f: [E; STAGES] = std::array::from_fn(|_| tr.squeeze_e());
    let phit = PhiTab::new(&f);
    let tgt = target(&f, &sl);
    let wv = par::collect_vec(eq_hi.len(), 1 << 12, |i| phit.apply(eq_hi[i]));
    let qe = par::collect_vec(q.len(), 1 << 14, |i| E::from_k(K(q[i])));
    let (rs_polys, r2, _wfin, qfin) = product_sumcheck(wv, qe, tgt, KIND_RS, &mut tr);
    lap("ringswitch", &mut t);

    // Ligero evaluation (§5.4)
    let a = eq_table(&r2[sh.lk..]);
    let v = combine_rows(q, m, k, &a);
    debug_assert_eq!(
        {
            let b = eq_table(&r2[..sh.lk]);
            (0..k).fold(E::ZERO, |acc, j| acc + b[j] * v[j])
        },
        qfin
    );
    let _ = qfin;
    tr.absorb(0x08, &bytes_of(&v));
    let idx = tr.squeeze_indices(T_COLS, ln);

    // bytes (§7)
    let mut bytes = leaf_header(s, n, &wit.h);
    bytes.extend_from_slice(&root);
    bytes.extend_from_slice(&bytes_of(&ubar));
    for g in &out.polys {
        bytes.extend_from_slice(&bytes_of(g));
    }
    bytes.extend_from_slice(&bytes_of(&out.v));
    for g in &inn.polys {
        bytes.extend_from_slice(&bytes_of(g));
    }
    bytes.extend_from_slice(&bytes_of(&sl));
    for g in &rs_polys {
        bytes.extend_from_slice(&bytes_of(g));
    }
    bytes.extend_from_slice(&bytes_of(&v));
    for &c in &idx {
        bytes.extend_from_slice(&col_bytes(c));
        for lab in tree.path(c) {
            bytes.extend_from_slice(&lab);
        }
    }
    assert_eq!(bytes.len(), leaf_size(n));
    if let Some(tc) = trace {
        *tc = LeafTrace {
            tau: tau.clone(),
            r_x: out.r_x.clone(),
            rho,
            r_y: inn.r_y.clone(),
            f: f.to_vec(),
            r2: r2.clone(),
            w: wit.w.clone(),
            a: wit.a.clone(),
            b: wit.b.clone(),
            c: wit.c.clone(),
            h: wit.h,
        };
    }
    lap("open", &mut t);
    tm.push(("total", t0.elapsed().as_secs_f64()));
    (bytes, Timings(tm), tr.log)
}
