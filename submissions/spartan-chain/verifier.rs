//! The native verifier: BLUEPRINT-R1's `check` (§1.2–§1.3, §3–§6), the self-check oracle of the
//! Rust prover until the compiled Lean `check` exists. Same decisions, same reads, same oracle.

use crate::blake2s::{leaf_stmt, node_stmt, Digest};
use crate::chain::{leaf_size, matrix_eval, pub_mle, Shape, CHAIN_CAP, PROOF_CAP, T_COLS};
use crate::circuit::Circuit;
use crate::field::{E, K};
use crate::mle::{eq_ee, eq_table, horner};
use crate::ringswitch::{coeffs, target, weight_mle, STAGES};
use crate::rs::Code;
use crate::transcript::{climb, Label, Transcript};

/// `Vb c π = (π.size ≤ proofCap) && check c π`.
pub fn vb(circ: &Circuit, c: &Digest, pi: &[u8]) -> bool {
    pi.len() <= PROOF_CAP && check(circ, c, pi)
}

pub fn word0(pi: &[u8]) -> Option<u64> {
    if pi.len() < 8 {
        None
    } else {
        Some(u64::from_le_bytes(pi[..8].try_into().unwrap()))
    }
}

/// `check c π` (§1.2), recursive on size.
pub fn check(circ: &Circuit, c: &Digest, pi: &[u8]) -> bool {
    match word0(pi) {
        Some(0) => check_leaf(circ, c, pi).is_ok(),
        Some(1) => check_node(circ, c, pi),
        _ => false,
    }
}

/// A node proof decoded canonically: `(c1, c2, π1, π2)`, or `None` unless `π` is exactly
/// `encode (.node c1 c2 π1 π2)` with both children within `proofCap`.
pub fn decode_node(pi: &[u8]) -> Option<(Digest, Digest, &[u8], &[u8])> {
    if word0(pi)? != 1 || pi.len() < 80 {
        return None;
    }
    let c1: Digest = pi[8..40].try_into().unwrap();
    let c2: Digest = pi[40..72].try_into().unwrap();
    let rd = |o: usize| -> Option<u64> { pi.get(o..o + 8).map(|b| u64::from_le_bytes(b.try_into().unwrap())) };
    let l1 = rd(72)?;
    if l1 > PROOF_CAP as u64 {
        return None;
    }
    let l1 = l1 as usize;
    let p1 = l1.div_ceil(8) * 8;
    let o2 = 80 + p1;
    let l2 = rd(o2)?;
    if l2 > PROOF_CAP as u64 {
        return None;
    }
    let l2 = l2 as usize;
    let p2 = l2.div_ceil(8) * 8;
    let s2 = o2 + 8;
    if pi.len() != s2 + p2 {
        return None;
    }
    if pi[80 + l1..80 + p1].iter().any(|&b| b != 0) || pi[s2 + l2..s2 + p2].iter().any(|&b| b != 0) {
        return None;
    }
    Some((c1, c2, &pi[80..80 + l1], &pi[s2..s2 + l2]))
}

/// `encode (.node c1 c2 π1 π2)`: `u64 1 ‖ c1 ‖ c2 ‖ u64 |π1| ‖ π1 ‖ 0-pad ‖ u64 |π2| ‖ π2 ‖ 0-pad`.
pub fn encode_node(c1: &Digest, c2: &Digest, p1: &[u8], p2: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(96 + p1.len() + p2.len());
    v.extend_from_slice(&1u64.to_le_bytes());
    v.extend_from_slice(c1);
    v.extend_from_slice(c2);
    for p in [p1, p2] {
        v.extend_from_slice(&(p.len() as u64).to_le_bytes());
        v.extend_from_slice(p);
        v.resize(v.len().div_ceil(8) * 8, 0);
    }
    v
}

pub fn check_node(circ: &Circuit, c: &Digest, pi: &[u8]) -> bool {
    match decode_node(pi) {
        Some((c1, c2, p1, p2)) => *c == node_stmt(&c1, &c2) && check(circ, &c1, p1) && check(circ, &c2, p2),
        None => false,
    }
}

/// `leafProg c π` run under `blake2sOracle`, with the reason for a rejection.
pub fn check_leaf(circ: &Circuit, c: &Digest, pi: &[u8]) -> Result<usize, String> {
    if pi.len() < 80 {
        return Err("leaf shorter than 80 bytes".into());
    }
    let s: Digest = pi[8..40].try_into().unwrap();
    let n = u64::from_le_bytes(pi[40..48].try_into().unwrap());
    let h: Digest = pi[48..80].try_into().unwrap();
    if n > CHAIN_CAP {
        return Err("n > chainCap".into());
    }
    if pi.len() != leaf_size(n) {
        return Err(format!("size {} != leafSize {}", pi.len(), leaf_size(n)));
    }
    if *c != leaf_stmt(&h, n) {
        return Err("statement is not leafStmt h n".into());
    }
    if n == 0 {
        return if h == s { Ok(0) } else { Err("n = 0 and h != s".into()) };
    }
    verify_snark(circ, &s, n, &h, &pi[80..])
}

struct Cursor<'a> {
    b: &'a [u8],
    o: usize,
}

impl<'a> Cursor<'a> {
    fn take(&mut self, n: usize) -> &'a [u8] {
        let r = &self.b[self.o..self.o + n];
        self.o += n;
        r
    }
    fn es(&mut self, n: usize) -> (Vec<E>, &'a [u8]) {
        let raw = self.take(24 * n);
        ((0..n).map(|i| E::from_bytes(&raw[24 * i..24 * i + 24])).collect(), raw)
    }
}

/// Run the sumcheck verifier rounds: absorb each polynomial, check `g(0) + g(1) = claim`,
/// squeeze the challenge, set `claim = g(r)`.
fn rounds(cur: &mut Cursor, tr: &mut Transcript, kind: u8, count: usize, deg: usize, mut claim: E) -> Result<(Vec<E>, E), String> {
    let mut r = vec![];
    for l in 0..count {
        let (g, raw) = cur.es(deg + 1);
        tr.absorb(kind, raw);
        let mut sum = g[0];
        for &ci in &g {
            sum += ci;
        }
        if sum != claim {
            return Err(format!("sumcheck kind {kind:02x} round {l}: g(0) + g(1) != claim"));
        }
        let rl = tr.squeeze_e();
        claim = horner(&g, rl);
        r.push(rl);
    }
    Ok((r, claim))
}

/// The SNARK verifier of §3–§6 on `π_S(n)`; returns the number of oracle queries made.
pub fn verify_snark(circ: &Circuit, s: &Digest, n: u64, h: &Digest, ps: &[u8]) -> Result<usize, String> {
    let sh = Shape::new(n);
    let (m, k, ln, ell, kp) = (sh.m, sh.k, sh.ln, sh.ell, sh.kappa);
    assert_eq!(ps.len(), sh.snark_size());
    let mut cur = Cursor { b: ps, o: 0 };
    let mut tr = Transcript::new(s, n, h, false);
    // 1–4: root, proximity coefficients, ū
    let root: Label = cur.take(31).try_into().unwrap();
    tr.absorb(0x01, &root);
    let rc: Vec<E> = (0..m).map(|_| tr.squeeze_e()).collect();
    let (ubar, raw) = cur.es(k);
    tr.absorb(0x02, raw);
    // 5–6: outer
    let tau: Vec<E> = (0..ell).map(|_| tr.squeeze_e()).collect();
    let (r_x, claim) = rounds(&mut cur, &mut tr, 0x03, ell, 3, E::ZERO)?;
    let (vabc, raw) = cur.es(3);
    if claim != eq_ee(&tau, &r_x) * (vabc[0] * vabc[1] + vabc[2]) {
        return Err("outer final check".into());
    }
    // 7–8: inner
    tr.absorb(0x04, raw);
    let rho = tr.squeeze_e();
    let (r_y, claim) = rounds(&mut cur, &mut tr, 0x05, ell, 2, vabc[0] + rho * vabc[1] + rho * rho * vabc[2])?;
    // 9: slices
    let (sl, raw) = cur.es(64);
    tr.absorb(0x06, raw);
    let f: [E; STAGES] = std::array::from_fn(|_| tr.squeeze_e());
    let r_u = &r_y[..14 + kp];
    let el = eq_table(&r_u[..6]);
    let mut wt = E::ZERO;
    for i in 0..64 {
        wt += el[i] * sl[i];
    }
    let ytop = r_y[14 + kp];
    let zt = (E::ONE + ytop) * wt + ytop * pub_mle(s, h, r_u);
    if claim != matrix_eval(circ, &sh, &r_x, &r_y, rho) * zt {
        return Err("inner final check".into());
    }
    // 10: ring switch
    let r_hi = &r_u[6..];
    let (r2, claim) = rounds(&mut cur, &mut tr, 0x07, sh.lq(), 2, target(&f, &sl))?;
    // 11: v
    let (v, raw) = cur.es(k);
    let b = eq_table(&r2[..sh.lk]);
    let mut vp = E::ZERO;
    for j in 0..k {
        vp += b[j] * v[j];
    }
    if claim != weight_mle(&coeffs(&f), r_hi, &r2) * vp {
        return Err("ring-switch final check".into());
    }
    tr.absorb(0x08, raw);
    // 12–13: columns
    let idx = tr.squeeze_indices(T_COLS, ln);
    let a = eq_table(&r2[sh.lk..]);
    let code = Code::new(sh.lk, ln);
    let mut merkle_queries = 0;
    for (ci, &c) in idx.iter().enumerate() {
        let col = cur.take(8 * m);
        let path: Vec<Label> = (0..ln).map(|_| cur.take(31).try_into().unwrap()).collect();
        merkle_queries += 1 + ln;
        if climb(c, col, &path) != root {
            return Err(format!("column {ci} (index {c}): Merkle path"));
        }
        let basis = code.basis_at(c);
        let mut cr = E::ZERO;
        let mut ca = E::ZERO;
        for i in 0..m {
            let x = K::from_bytes(&col[8 * i..8 * i + 8]);
            cr += rc[i].mul_k(x);
            ca += a[i].mul_k(x);
        }
        if Code::enc_at(&ubar, &basis) != cr {
            return Err(format!("column {ci} (index {c}): proximity test"));
        }
        if Code::enc_at(&v, &basis) != ca {
            return Err(format!("column {ci} (index {c}): evaluation test"));
        }
    }
    assert_eq!(cur.o, ps.len());
    Ok(tr.queries + merkle_queries)
}
