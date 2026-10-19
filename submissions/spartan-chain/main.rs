//! `spartan-chain-prover`: the native prover of the honest SNARK entry (BLUEPRINT-R1 §11).
//!
//!   tree DIR                    DESIGN-v3 §6.3: DIR/leaves.json {"n": N, "starts": [hex, ...]} ->
//!                               DIR/proofs/L<i>.bin, DIR/proofs/N<level>_<j>.bin, DIR/root.bin
//!   node DIR                    DIR/child{1,2}.{stmt,proof} -> DIR/proof.bin
//!   prove-leaf START.hex N OUT  one leaf proof; prints its statement
//!   verify STMT.hex PROOF.bin   the native `Vb` (self-check); exit 0 accept, 1 reject, 2 usage/IO
//!   dump-field | dump-circuit | dump-walk | dump-encode | dump-transcript   KAT text to stdout
//!   dump-proof DIR              KAT leaf proofs (n = 1, 2, 16, 64) into DIR, summary to stdout
//!   check-leaf STMT.hex PROOF   diagnostic: the leaf branch without the proofCap guard
//!   bench-field                 field multiplication micro-benchmark
//!
//! Set SPARTAN_VERBOSE=1 for per-phase timings on stderr, SPARTAN_THREADS to bound threads.

// Some helpers are used only by the tests and the known-answer dumps.
#![allow(dead_code)]

mod blake2s;
mod chain;
mod circuit;
mod field;
mod kat;
mod mle;
mod par;
mod prover;
mod ringswitch;
mod rs;
mod sumcheck;
mod transcript;
mod verifier;

use std::path::Path;
use std::process::ExitCode;
use std::time::Instant;

use blake2s::{chain_end, leaf_stmt, node_stmt, Digest};
use circuit::Circuit;

fn verbose() -> bool {
    std::env::var("SPARTAN_VERBOSE").map(|v| v != "0").unwrap_or(false)
}

fn parse_hex32(s: &str) -> Option<Digest> {
    let s = s.trim();
    if s.len() != 64 {
        return None;
    }
    let mut d = [0u8; 32];
    for i in 0..32 {
        d[i] = u8::from_str_radix(s.get(2 * i..2 * i + 2)?, 16).ok()?;
    }
    Some(d)
}

fn read_stmt(path: &Path) -> Result<Digest, String> {
    let b = std::fs::read(path).map_err(|e| format!("{}: {e}", path.display()))?;
    if b.len() == 32 {
        return Ok(b.try_into().unwrap());
    }
    std::str::from_utf8(&b)
        .ok()
        .and_then(parse_hex32)
        .ok_or_else(|| format!("{}: not a statement (64 hex digits or 32 bytes)", path.display()))
}

/// `{"n": N, "starts": ["<64 hex>", ...]}` (the S2a format).
fn parse_leaves(text: &str) -> Result<(u64, Vec<Digest>), String> {
    let bad = || "leaves.json: expected {\"n\": N, \"starts\": [hex, ...]}".to_string();
    let ni = text.find("\"n\"").ok_or_else(bad)?;
    let rest = text[ni + 3..].trim_start().strip_prefix(':').ok_or_else(bad)?.trim_start();
    let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
    let n: u64 = digits.parse().map_err(|_| bad())?;
    let si = text.find("\"starts\"").ok_or_else(bad)?;
    let open = si + text[si..].find('[').ok_or_else(bad)?;
    let close = open + text[open..].find(']').ok_or_else(bad)?;
    let mut starts = vec![];
    for part in text[open + 1..close].split(',') {
        let p = part.trim();
        if p.is_empty() {
            continue;
        }
        let p = p.strip_prefix('"').and_then(|p| p.strip_suffix('"')).ok_or_else(bad)?;
        starts.push(parse_hex32(p).ok_or_else(bad)?);
    }
    if n > chain::CHAIN_CAP || starts.is_empty() || !starts.len().is_power_of_two() {
        return Err("leaves.json: n in [0, 2^20] and a power of two of 32-byte starts".into());
    }
    Ok((n, starts))
}

fn prove_leaf_logged(circ: &Circuit, s: &Digest, n: u64) -> Vec<u8> {
    let (pi, tm, _) = prover::prove_leaf(circ, s, n, false);
    if verbose() {
        eprintln!("prove-leaf n={n} bytes={} {}", pi.len(), tm.report());
    }
    pi
}

fn cmd_tree(dir: &Path) -> Result<(), String> {
    let text = std::fs::read_to_string(dir.join("leaves.json")).map_err(|e| format!("leaves.json: {e}"))?;
    let (n, starts) = parse_leaves(&text)?;
    let circ = Circuit::build();
    let pdir = dir.join("proofs");
    std::fs::create_dir_all(&pdir).map_err(|e| e.to_string())?;
    let wr = |name: String, b: &[u8]| std::fs::write(pdir.join(name), b).map_err(|e| e.to_string());
    let mut level: Vec<(Digest, Vec<u8>)> = vec![];
    for (i, s) in starts.iter().enumerate() {
        let pi = prove_leaf_logged(&circ, s, n);
        let h = chain_end(s, n);
        wr(format!("L{i}.bin"), &pi)?;
        level.push((leaf_stmt(&h, n), pi));
    }
    let mut lv = 0;
    while level.len() > 1 {
        lv += 1;
        let mut next = vec![];
        for (j, pair) in level.chunks(2).enumerate() {
            let ((c1, p1), (c2, p2)) = (&pair[0], &pair[1]);
            let pi = verifier::encode_node(c1, c2, p1, p2);
            wr(format!("N{lv}_{j}.bin"), &pi)?;
            next.push((node_stmt(c1, c2), pi));
        }
        level = next;
    }
    std::fs::write(dir.join("root.bin"), &level[0].1).map_err(|e| e.to_string())?;
    Ok(())
}

fn cmd_node(dir: &Path) -> Result<(), String> {
    let c1 = read_stmt(&dir.join("child1.stmt"))?;
    let c2 = read_stmt(&dir.join("child2.stmt"))?;
    let p1 = std::fs::read(dir.join("child1.proof")).map_err(|e| format!("child1.proof: {e}"))?;
    let p2 = std::fs::read(dir.join("child2.proof")).map_err(|e| format!("child2.proof: {e}"))?;
    std::fs::write(dir.join("proof.bin"), verifier::encode_node(&c1, &c2, &p1, &p2)).map_err(|e| e.to_string())
}

fn run(args: &[String]) -> Result<ExitCode, String> {
    let a: Vec<&str> = args.iter().map(|s| s.as_str()).collect();
    match a.as_slice() {
        ["tree", dir] => cmd_tree(Path::new(dir)).map(|_| ExitCode::SUCCESS),
        ["node", dir] => cmd_node(Path::new(dir)).map(|_| ExitCode::SUCCESS),
        ["prove-leaf", start, n, out] => {
            let s = read_stmt(Path::new(start))?;
            let n: u64 = n.parse().map_err(|_| "N: not a number".to_string())?;
            if n > chain::CHAIN_CAP {
                return Err("N > chainCap".into());
            }
            let circ = Circuit::build();
            let pi = prove_leaf_logged(&circ, &s, n);
            std::fs::write(out, &pi).map_err(|e| e.to_string())?;
            let h: Digest = pi[48..80].try_into().unwrap();
            println!("{}", kat::hex(&leaf_stmt(&h, n)));
            Ok(ExitCode::SUCCESS)
        }
        ["verify", stmt, proof] => {
            let c = read_stmt(Path::new(stmt))?;
            let pi = std::fs::read(proof).map_err(|e| format!("{proof}: {e}"))?;
            let circ = Circuit::build();
            let t = Instant::now();
            let ok = verifier::vb(&circ, &c, &pi);
            if verbose() {
                let why = if verifier::word0(&pi) == Some(0) && pi.len() <= chain::PROOF_CAP {
                    match verifier::check_leaf(&circ, &c, &pi) {
                        Ok(q) => format!("queries={q}"),
                        Err(e) => e,
                    }
                } else {
                    String::new()
                };
                eprintln!("verify {} bytes={} time={:.4}s {why}", if ok { "ACCEPT" } else { "REJECT" }, pi.len(), t.elapsed().as_secs_f64());
            }
            Ok(if ok { ExitCode::SUCCESS } else { ExitCode::from(1) })
        }
        ["check-leaf", stmt, proof] => {
            // diagnostic: `leafProg` without the `proofCap` guard of `Vb` (for n > 4096)
            let c = read_stmt(Path::new(stmt))?;
            let pi = std::fs::read(proof).map_err(|e| format!("{proof}: {e}"))?;
            let circ = Circuit::build();
            let t = Instant::now();
            let r = verifier::check_leaf(&circ, &c, &pi);
            eprintln!("check-leaf {:?} bytes={} time={:.4}s", r, pi.len(), t.elapsed().as_secs_f64());
            Ok(if r.is_ok() { ExitCode::SUCCESS } else { ExitCode::from(1) })
        }
        ["bench-field"] => {
            let mut a = field::E([1, 2, 3]);
            let b = field::E([0x1234_5678_9abc_def1, 0xfedc_ba98_7654_3211, 0x0f0f_0f0f_0f0f_0f0f]);
            let t = Instant::now();
            for _ in 0..10_000_000 {
                a = a * b + b;
            }
            println!("E mul+add: {:.1} ns ({:?})", t.elapsed().as_secs_f64() * 1e9 / 1e7, a.0[0] & 1);
            let mut x = 12345u64;
            let t = Instant::now();
            for _ in 0..10_000_000 {
                x = (field::K(x) * field::K(0x9E37_79B9_7F4A_7C15)).0 ^ 1;
            }
            println!("K mul: {:.1} ns ({})", t.elapsed().as_secs_f64() * 1e9 / 1e7, x & 1);
            let tab = field::ETab::new(b);
            let t = Instant::now();
            for _ in 0..10_000_000 {
                a = tab.mul(a) + b;
            }
            println!("E fixed mul: {:.1} ns ({})", t.elapsed().as_secs_f64() * 1e9 / 1e7, a.0[0] & 1);
            Ok(ExitCode::SUCCESS)
        }
        ["dump-field"] => {
            print!("{}", kat::dump_field());
            Ok(ExitCode::SUCCESS)
        }
        ["dump-circuit"] => {
            print!("{}", kat::dump_circuit(&Circuit::build()));
            Ok(ExitCode::SUCCESS)
        }
        ["dump-walk"] => {
            print!("{}", kat::dump_walk(&Circuit::build()));
            Ok(ExitCode::SUCCESS)
        }
        ["dump-encode"] => {
            print!("{}", kat::dump_encode());
            Ok(ExitCode::SUCCESS)
        }
        ["dump-transcript"] => {
            print!("{}", kat::dump_transcript(&Circuit::build()));
            Ok(ExitCode::SUCCESS)
        }
        ["dump-proof", dir] => {
            print!("{}", kat::dump_proofs(&Circuit::build(), dir).map_err(|e| e.to_string())?);
            Ok(ExitCode::SUCCESS)
        }
        _ => Err("usage: spartan-chain-prover tree DIR | node DIR | prove-leaf START.hex N OUT.bin | \
                  verify STMT.hex PROOF.bin | dump-field | dump-circuit | dump-walk | dump-encode | \
                  dump-transcript | dump-proof DIR"
            .into()),
    }
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    match run(&args) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("spartan-chain-prover: {e}");
            ExitCode::from(2)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::chain::leaf_size;
    use crate::verifier::{check, check_leaf, encode_node, vb};

    fn start(i: u8) -> Digest {
        std::array::from_fn(|j| (j as u8).wrapping_mul(13).wrapping_add(i))
    }

    fn roundtrip(n: u64) {
        let circ = Circuit::build();
        let s = start(n as u8);
        let (pi, _, _) = prover::prove_leaf(&circ, &s, n, false);
        assert_eq!(pi.len(), leaf_size(n));
        let h = chain_end(&s, n);
        let c = leaf_stmt(&h, n);
        assert!(vb(&circ, &c, &pi), "n = {n}: {:?}", check_leaf(&circ, &c, &pi));
        // negative: one flipped byte in every field of §1.1/§7 is rejected, plus random bytes
        let sh = chain::Shape::new(n);
        let mut regions: Vec<(&str, usize)> =
            vec![("tag", 0), ("s", 8), ("n", 40), ("h", 48), ("root", 80)];
        let mut o = 80 + 31;
        for (name, len) in [
            ("ubar", 24 * sh.k),
            ("outer", 96 * sh.ell),
            ("vabc", 72),
            ("inner", 72 * sh.ell),
            ("slices", 1536),
            ("ringswitch", 72 * sh.lq()),
            ("v", 24 * sh.k),
        ] {
            regions.push((name, o));
            regions.push((name, o + len - 1));
            o += len;
        }
        regions.push(("column", o));
        regions.push(("path", o + 8 * sh.m));
        regions.push(("last", pi.len() - 1));
        let mut rng = 0x1234_5678u64 ^ n;
        for _ in 0..16 {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            regions.push(("random", (rng >> 20) as usize % pi.len()));
        }
        for (name, pos) in regions {
            for bit in [0u8, 7] {
                let mut bad = pi.clone();
                bad[pos] ^= 1 << bit;
                assert!(!vb(&circ, &c, &bad), "n = {n}: flipped {name} byte {pos} bit {bit} accepted");
            }
        }
        // canaries: appended byte, removed last byte, wrong statement
        let mut longer = pi.clone();
        longer.push(0);
        assert!(!vb(&circ, &c, &longer));
        assert!(!vb(&circ, &c, &pi[..pi.len() - 1]));
        let mut c2 = c;
        c2[0] ^= 1;
        assert!(!vb(&circ, &c2, &pi));
        // deterministic: the same proof again
        let (pi2, _, _) = prover::prove_leaf(&circ, &s, n, false);
        assert_eq!(pi, pi2);
    }

    #[test]
    fn roundtrip_n1() {
        roundtrip(1);
    }
    #[test]
    fn roundtrip_n2() {
        roundtrip(2);
    }
    #[test]
    fn roundtrip_n3() {
        roundtrip(3);
    }
    #[test]
    fn roundtrip_n16() {
        roundtrip(16);
    }
    #[test]
    fn roundtrip_n64() {
        roundtrip(64);
    }

    #[test]
    fn n0_leaf() {
        let circ = Circuit::build();
        let s = start(7);
        let (pi, _, _) = prover::prove_leaf(&circ, &s, 0, false);
        assert_eq!(pi.len(), 80);
        assert!(vb(&circ, &leaf_stmt(&s, 0), &pi));
        let mut bad = pi.clone();
        bad[60] ^= 1;
        assert!(!vb(&circ, &leaf_stmt(&s, 0), &bad));
    }

    /// The r = 2, n = 16 smoke tree: every node and the root verify; canaries reject.
    #[test]
    fn smoke_tree_r2_n16() {
        let dir = std::env::temp_dir().join(format!("spartan-chain-tree-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let starts: Vec<Digest> = (0..4).map(start).collect();
        let json = format!(
            "{{\"n\": 16, \"starts\": [{}]}}",
            starts.iter().map(|s| format!("\"{}\"", kat::hex(s))).collect::<Vec<_>>().join(", ")
        );
        std::fs::write(dir.join("leaves.json"), json).unwrap();
        cmd_tree(&dir).unwrap();
        let circ = Circuit::build();
        let rd = |p: &str| std::fs::read(dir.join(p)).unwrap();
        let leaves: Vec<Digest> = starts.iter().map(|s| leaf_stmt(&chain_end(s, 16), 16)).collect();
        let n1 = [node_stmt(&leaves[0], &leaves[1]), node_stmt(&leaves[2], &leaves[3])];
        let root = node_stmt(&n1[0], &n1[1]);
        for i in 0..4 {
            assert!(vb(&circ, &leaves[i], &rd(&format!("proofs/L{i}.bin"))));
        }
        for j in 0..2 {
            assert!(vb(&circ, &n1[j], &rd(&format!("proofs/N1_{j}.bin"))));
        }
        let rp = rd("root.bin");
        assert_eq!(rp, rd("proofs/N2_0.bin"));
        assert_eq!(rp.len(), 575_112);
        assert!(vb(&circ, &root, &rp));
        // canaries on the root
        let mut a = rp.clone();
        a.push(0);
        assert!(!vb(&circ, &root, &a));
        assert!(!vb(&circ, &root, &rp[..rp.len() - 1]));
        let mut c = root;
        c[31] ^= 0x80;
        assert!(!vb(&circ, &c, &rp));
        let swapped = encode_node(&n1[1], &n1[0], &rd("proofs/N1_0.bin"), &rd("proofs/N1_1.bin"));
        assert!(!vb(&circ, &root, &swapped));
        // a flipped byte deep inside a leaf inside the root
        let mut d = rp.clone();
        let mid = d.len() / 3;
        d[mid] ^= 4;
        assert!(!check(&circ, &root, &d));
        // node command
        std::fs::write(dir.join("child1.stmt"), kat::hex(&n1[0])).unwrap();
        std::fs::write(dir.join("child2.stmt"), n1[1]).unwrap();
        std::fs::write(dir.join("child1.proof"), rd("proofs/N1_0.bin")).unwrap();
        std::fs::write(dir.join("child2.proof"), rd("proofs/N1_1.bin")).unwrap();
        cmd_node(&dir).unwrap();
        assert_eq!(rd("proof.bin"), rp);
        std::fs::remove_dir_all(&dir).unwrap();
    }
}
