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
use crate::prover::prove_leaf;
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
        let (a1, b1) = circ.walk(&e, &wt, false);
        writeln!(o, "walk {i} {} {} {} {}", hex_e(a), hex_e(b), hex_e(a1), hex_e(b1)).unwrap();
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
