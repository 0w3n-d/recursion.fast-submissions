//! The Fiat–Shamir transcript (BLUEPRINT-R1 §6) and the Merkle tree (§5.3), both over the oracle
//! `H(q) = blake2s256(0x52 ‖ q)`. Every oracle call can be logged (`dump-transcript`).

use crate::blake2s::{oracle, Digest};
use crate::field::{ch_e, E};
use crate::par;

pub type Label = [u8; 31];

pub fn trunc(d: &Digest) -> Label {
    d[..31].try_into().unwrap()
}

pub struct Transcript {
    pub st: Digest,
    /// `(operation, kind, state after)` when logging
    pub log: Option<Vec<(String, Digest)>>,
    pub queries: usize,
}

impl Transcript {
    /// `st ← H(0x10 ‖ s ‖ enc64 n ‖ h)`.
    pub fn new(s: &Digest, n: u64, h: &Digest, logging: bool) -> Transcript {
        let st = oracle(&[&[0x10], s, &n.to_le_bytes(), h]);
        let mut t = Transcript { st, log: if logging { Some(vec![]) } else { None }, queries: 1 };
        t.note("seed".into());
        t
    }
    fn note(&mut self, what: String) {
        let st = self.st;
        if let Some(l) = self.log.as_mut() {
            l.push((what, st));
        }
    }
    /// `absorb(st, kind, msg) := H(0x20 ‖ st ‖ kind ‖ msg)`.
    pub fn absorb(&mut self, kind: u8, msg: &[u8]) {
        self.st = oracle(&[&[0x20], &self.st, &[kind], msg]);
        self.queries += 1;
        self.note(format!("absorb {:02x} {}", kind, msg.len()));
    }
    /// `squeeze(st) := H(0x30 ‖ st)`; the answer is the new state and the challenge source.
    pub fn squeeze(&mut self) -> Digest {
        self.st = oracle(&[&[0x30], &self.st]);
        self.queries += 1;
        self.note("squeeze".into());
        self.st
    }
    pub fn squeeze_e(&mut self) -> E {
        let a = self.squeeze();
        ch_e(&a)
    }
    /// `t` column indices in `[0, 2^ln)` from `⌈t/cnt⌉` answers (§6.1).
    pub fn squeeze_indices(&mut self, t: usize, ln: usize) -> Vec<usize> {
        let cnt = 256 / ln;
        let mut out = Vec::with_capacity(t);
        while out.len() < t {
            let a = self.squeeze();
            for i in 0..cnt {
                if out.len() == t {
                    break;
                }
                let mut v = 0usize;
                for b in 0..ln {
                    let bit = i * ln + b;
                    v |= (((a[bit / 8] >> (bit % 8)) & 1) as usize) << b;
                }
                out.push(v);
            }
        }
        out
    }
}

/// `λ(c) = [H(0x00 ‖ column bytes)]_31`.
pub fn leaf_label(col: &[u8]) -> Label {
    trunc(&oracle(&[&[0x00], col]))
}

/// `λ(v) = [H(0x01 ‖ λ(left) ‖ λ(right))]_31`.
pub fn node_label(l: &Label, r: &Label) -> Label {
    trunc(&oracle(&[&[0x01], l, r]))
}

/// A Merkle tree over `2^ln` labels: `levels[0]` the leaves, `levels[ln]` the root.
pub struct Merkle {
    pub levels: Vec<Vec<Label>>,
}

impl Merkle {
    pub fn build(leaves: Vec<Label>) -> Merkle {
        let mut levels = vec![leaves];
        while levels.last().unwrap().len() > 1 {
            let prev = levels.last().unwrap();
            let mut next = vec![[0u8; 31]; prev.len() / 2];
            par::fill(&mut next, 256, |i| node_label(&prev[2 * i], &prev[2 * i + 1]));
            levels.push(next);
        }
        Merkle { levels }
    }
    pub fn root(&self) -> Label {
        self.levels.last().unwrap()[0]
    }
    /// The `ℓ_N` sibling labels of leaf `c`, bottom-up.
    pub fn path(&self, c: usize) -> Vec<Label> {
        let mut out = vec![];
        let mut i = c;
        for l in 0..self.levels.len() - 1 {
            out.push(self.levels[l][i ^ 1]);
            i >>= 1;
        }
        out
    }
}

/// Recompute the root from a column's bytes and its path (`V`'s climb, §5.3).
pub fn climb(c: usize, col: &[u8], path: &[Label]) -> Label {
    let mut cur = leaf_label(col);
    for (l, sib) in path.iter().enumerate() {
        cur = if (c >> l) & 1 == 0 { node_label(&cur, sib) } else { node_label(sib, &cur) };
    }
    cur
}
