//! Known-answer dumps (BLUEPRINT-R1 §11.3). The Lean `spartan-run dump-*` must write the same
//! text; the formats are fixed in `docs/snark-baseline/reports/rust-prover.md` §KAT.
//!
//! Inputs come from `katRand tag i = blake2s256("spartan-chain-kat/" ‖ tag ‖ 0x00 ‖ enc64 i)`
//! (plain BLAKE2s, not the oracle): a `K` element is its bytes 0..8 (little-endian word), an `E`
//! element its bytes 0..24 (`chE`).

use std::fmt::Write as _;

use crate::blake2s::{blake2s256, leaf_stmt, Blake2s, Digest};
use crate::circuit::{Circuit, BLOCK};
use crate::field::{ch_e, hex_e, hex_k, E, K};
use crate::mle::eq_table;
use crate::chain::{matrix_table_naive, pub_bit, Shape};
use crate::mle::{eq_ee, mle_eval};
use crate::prover::{prove_leaf, prove_leaf_traced, LeafTrace};
use crate::ringswitch::{coeffs, phi, target, weight_mle};
use crate::sumcheck::product_rounds;
use crate::transcript::Transcript;
use crate::rs::Code;

pub fn kat_rand(tag: &str, i: u64) -> Digest {
    Blake2s::new()
        .update(b"spartan-chain-kat/")
        .update(tag.as_bytes())
        .update(&[0])
        .update(&i.to_le_bytes())
        .finalize()
}
pub fn rand_k(tag: &str, i: u64) -> K {
    K::from_bytes(&kat_rand(tag, i))
}
pub fn rand_e(tag: &str, i: u64) -> E {
    ch_e(&kat_rand(tag, i))
}
pub fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{:02x}", x)).collect()
}

pub fn dump_field() -> String {
    let mut o = String::new();
    for i in 0..1000 {
        let (a, b) = (rand_k("field-k-a", i), rand_k("field-k-b", i));
        writeln!(o, "kmul {i} {} {} {} {} {}", hex_k(a), hex_k(b), hex_k(a * b), hex_k(a.sq()), hex(&a.to_bytes())).unwrap();
    }
    for i in 0..1000 {
        let (a, b) = (rand_e("field-e-a", i), rand_e("field-e-b", i));
        writeln!(o, "emul {i} {} {} {} {} {}", hex_e(a), hex_e(b), hex_e(a * b), hex_e(a.sq()), hex(&a.to_bytes())).unwrap();
    }
    o
}

fn bitset_bytes(v: &[u64; 256]) -> Vec<u8> {
    v.iter().flat_map(|w| w.to_le_bytes()).collect()
}

pub fn dump_circuit(circ: &Circuit) -> String {
    let rows = circ.row_bitsets();
    let mut o = String::new();
    for k in 0..BLOCK {
        let (a, b) = &rows[k];
        let na: u32 = a.iter().map(|w| w.count_ones()).sum();
        let nb: u32 = b.iter().map(|w| w.count_ones()).sum();
        writeln!(o, "{k} {na} {nb} {} {}", hex(&blake2s256(&bitset_bytes(a))), hex(&blake2s256(&bitset_bytes(b)))).unwrap();
    }
    o
}

pub fn dump_walk(circ: &Circuit) -> String {
    let mut o = String::new();
    for i in 0..8u64 {
        let rk: Vec<E> = (0..14).map(|l| rand_e("walk-rk", 14 * i + l)).collect();
        let rj: Vec<E> = (0..14).map(|l| rand_e("walk-rj", 14 * i + l)).collect();
        let (e, wt) = (eq_table(&rk), eq_table(&rj));
        let (a, b) = circ.walk(&e, &wt, true);
        writeln!(o, "walk {i} {} {}", hex_e(a), hex_e(b)).unwrap();
    }
    o
}

pub fn dump_encode() -> String {
    let (lk, ln) = (9usize, 12usize);
    let code = Code::new(lk, ln);
    let mut o = String::new();
    for i in 0..8u64 {
        let msg: Vec<E> = (0..(1u64 << lk)).map(|j| rand_e(&format!("encode-{i}"), j)).collect();
        for c in 0..(1usize << ln) {
            writeln!(o, "enc {i} {c} {}", hex_e(Code::enc_at(&msg, &code.basis_at(c)))).unwrap();
        }
    }
    o
}

pub fn transcript_leaf() -> (Digest, u64) {
    (std::array::from_fn(|i| i as u8), 2)
}

pub fn dump_transcript(circ: &Circuit) -> String {
    let (s, n) = transcript_leaf();
    let (_, _, log) = prove_leaf(circ, &s, n, true);
    let mut o = String::new();
    for (i, (what, st)) in log.unwrap().iter().enumerate() {
        writeln!(o, "{i} {what} {}", hex(st)).unwrap();
    }
    o
}

pub const PROOF_NS: [u64; 4] = [1, 2, 16, 64];

/// The fixed leaves of the proof KAT: `s = katRand "proof-start" n`.
pub fn proof_start(n: u64) -> Digest {
    kat_rand("proof-start", n)
}

pub fn dump_proofs(circ: &Circuit, dir: &str) -> std::io::Result<String> {
    std::fs::create_dir_all(dir)?;
    let mut o = String::new();
    for n in PROOF_NS {
        let s = proof_start(n);
        let (pi, _, _) = prove_leaf(circ, &s, n, false);
        let h: Digest = pi[48..80].try_into().unwrap();
        std::fs::write(format!("{dir}/kat-n{n}.bin"), &pi)?;
        writeln!(o, "proof {n} {} {} {} {}", hex(&s), hex(&leaf_stmt(&h, n)), pi.len(), hex(&blake2s256(&pi))).unwrap();
    }
    Ok(o)
}

fn hex_es(es: &[E]) -> String {
    es.iter().map(|e| hex_e(*e)).collect::<Vec<_>>().join(" ")
}

/// `eq` tables and a multilinear evaluation (`SpartanChainMLE`).
pub fn dump_mle() -> String {
    let r: Vec<E> = (0..10).map(|l| rand_e("mle-r", l)).collect();
    let r2: Vec<E> = (0..10).map(|l| rand_e("mle-r2", l)).collect();
    let t: Vec<E> = (0..1024).map(|u| rand_e("mle-t", u)).collect();
    let mut o = String::new();
    for (u, e) in eq_table(&r).iter().enumerate() {
        writeln!(o, "eq {u} {}", hex_e(*e)).unwrap();
    }
    writeln!(o, "mle {}", hex_e(mle_eval(&t, &r))).unwrap();
    writeln!(o, "eqpts {}", hex_e(eq_ee(&r, &r2))).unwrap();
    o
}

pub const TR_LENS: [usize; 8] = [0, 1, 31, 32, 33, 63, 64, 200];

/// The transcript primitives (`SpartanChainTranscript`): seed, absorbs of every framing length,
/// squeezes with their field challenges, index squeezes at `ℓ_N = 12` and `10`.
pub fn dump_transcript_ops() -> String {
    let (s, h, n) = (kat_rand("tr-s", 0), kat_rand("tr-h", 0), 5u64);
    let mut tr = Transcript::new(&s, n, &h, false);
    let mut o = String::new();
    writeln!(o, "seed {}", hex(&tr.st)).unwrap();
    for (i, &len) in TR_LENS.iter().enumerate() {
        let msg: Vec<u8> = (0..len).map(|j| kat_rand(&format!("tr-msg-{i}"), (j / 32) as u64)[j % 32]).collect();
        tr.absorb(i as u8 + 1, &msg);
        writeln!(o, "absorb {} {len} {}", i + 1, hex(&tr.st)).unwrap();
        for _ in 0..2 {
            let a = tr.squeeze();
            writeln!(o, "squeeze {} {}", hex(&a), hex_e(crate::field::ch_e(&a))).unwrap();
        }
    }
    for ln in [12usize, 10] {
        let idx = tr.squeeze_indices(260, ln);
        let list = idx.iter().map(|c| c.to_string()).collect::<Vec<_>>().join(",");
        writeln!(o, "idx {ln} {} {list}", hex(&tr.st)).unwrap();
    }
    o
}

/// Ring switching (`SpartanChainRingSwitch`): `c_k`, `Φ`, `T`, `W̃`.
pub fn dump_phi() -> String {
    let f: [E; 6] = std::array::from_fn(|p| rand_e("phi-f", p as u64));
    let mut o = String::new();
    for (k, c) in coeffs(&f).iter().enumerate() {
        writeln!(o, "ck {k} {}", hex_e(*c)).unwrap();
    }
    for i in 0..16 {
        let a = rand_e("phi-a", i);
        writeln!(o, "phi {i} {} {}", hex_e(a), hex_e(phi(&f, a))).unwrap();
    }
    let s: Vec<E> = (0..64).map(|i| rand_e("phi-s", i)).collect();
    writeln!(o, "target {}", hex_e(target(&f, &s))).unwrap();
    let r: Vec<E> = (0..9).map(|l| rand_e("phi-r", l)).collect();
    let r2: Vec<E> = (0..9).map(|l| rand_e("phi-r2", l)).collect();
    writeln!(o, "weight {}", hex_e(weight_mle(&coeffs(&f), &r, &r2))).unwrap();
    o
}

/// A product sumcheck on random tables with fixed challenges (`SpartanChainSumcheck.honest`).
pub fn dump_sumcheck() -> String {
    let f: Vec<E> = (0..256).map(|u| rand_e("sc-f", u)).collect();
    let g: Vec<E> = (0..256).map(|u| rand_e("sc-g", u)).collect();
    let claim = (0..256).fold(E::ZERO, |a, u| a + f[u] * g[u]);
    let mut l = 0u64;
    let (polys, _, ff, gf) = product_rounds(f, g, claim, &mut |_| {
        l += 1;
        rand_e("sc-r", l - 1)
    });
    let mut o = String::new();
    for (l, p) in polys.iter().enumerate() {
        writeln!(o, "round {l} {}", hex_es(p)).unwrap();
    }
    writeln!(o, "final {} {}", hex_e(ff), hex_e(gf)).unwrap();
    o
}

fn bits_hex(v: &[u64], nbits: usize) -> String {
    let bytes: Vec<u8> = v.iter().flat_map(|w| w.to_le_bytes()).collect();
    hex(&bytes[..nbits / 8])
}

/// The `n = 1` leaf of the proof KAT with its challenges and tables (`leaf-input.txt`, for the
/// Lean side to recompute from) and the values the Rust prover produced (`leaf-expect.txt`).
pub fn dump_leaf_trace(circ: &Circuit, dir: &str) -> std::io::Result<()> {
    std::fs::create_dir_all(dir)?;
    let n = 1u64;
    let s = proof_start(n);
    let sh = Shape::new(n);
    let mut tc = LeafTrace::default();
    let (pi, _, _) = prove_leaf_traced(circ, &s, n, false, Some(&mut tc));
    let ell = sh.ell;
    let mut inp = String::new();
    writeln!(inp, "s {}", hex(&s)).unwrap();
    writeln!(inp, "n {n}").unwrap();
    writeln!(inp, "h {}", hex(&tc.h)).unwrap();
    for (k, v) in [("tau", &tc.tau), ("rx", &tc.r_x), ("ry", &tc.r_y), ("f", &tc.f), ("r2", &tc.r2)] {
        writeln!(inp, "{k} {}", hex_es(v)).unwrap();
    }
    writeln!(inp, "rho {}", hex_e(tc.rho)).unwrap();
    for (k, v) in [("A", &tc.a), ("B", &tc.b), ("C", &tc.c)] {
        writeln!(inp, "{k} {}", bits_hex(v, 1 << ell)).unwrap();
    }
    // z = (w ‖ pub)
    let mut z = tc.w.clone();
    let mut pubw = vec![0u64; tc.w.len()];
    for u in 0..513 {
        if pub_bit(&s, &tc.h, u) {
            pubw[u / 64] |= 1 << (u % 64);
        }
    }
    z.extend_from_slice(&pubw);
    writeln!(inp, "z {}", bits_hex(&z, 1 << ell)).unwrap();
    writeln!(inp, "q {}", bits_hex(&tc.w, 1 << sh.lw)).unwrap();
    let m = matrix_table_naive(circ, &sh, &tc.r_x, tc.rho);
    writeln!(inp, "M {}", hex_es(&m)).unwrap();
    std::fs::write(format!("{dir}/leaf-input.txt"), inp)?;

    // the values as the Rust prover wrote them (§7 offsets)
    let ps = &pi[80..];
    let rd = |o: usize, cnt: usize| -> Vec<E> { (0..cnt).map(|i| E::from_bytes(&ps[o + 24 * i..])).collect() };
    let mut ex = String::new();
    writeln!(ex, "root {}", hex(&ps[..31])).unwrap();
    let mut o = 31;
    let ubar = rd(o, sh.k);
    o += 24 * sh.k;
    for (j, e) in ubar.iter().enumerate() {
        writeln!(ex, "ubar {j} {}", hex_e(*e)).unwrap();
    }
    for l in 0..ell {
        writeln!(ex, "outer {l} {}", hex_es(&rd(o, 4))).unwrap();
        o += 96;
    }
    writeln!(ex, "vabc {}", hex_es(&rd(o, 3))).unwrap();
    o += 72;
    for l in 0..ell {
        writeln!(ex, "inner {l} {}", hex_es(&rd(o, 3))).unwrap();
        o += 72;
    }
    let sl = rd(o, 64);
    for (i, e) in sl.iter().enumerate() {
        writeln!(ex, "slice {i} {}", hex_e(*e)).unwrap();
    }
    o += 1536;
    let f: [E; 6] = std::array::from_fn(|p| tc.f[p]);
    writeln!(ex, "target {}", hex_e(target(&f, &sl))).unwrap();
    for l in 0..sh.lq() {
        writeln!(ex, "rs {l} {}", hex_es(&rd(o, 3))).unwrap();
        o += 72;
    }
    std::fs::write(format!("{dir}/leaf-expect.txt"), ex)?;
    Ok(())
}
