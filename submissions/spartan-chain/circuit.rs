//! The chain block `chainBlock` (BLUEPRINT-R1 §2.2): leanerVM's BLAKE2s product circuit
//! (`LeanerVM/Protocol/Blake2sCircuit.lean` and `Protocol/ToArkLib/Flock/{Words,Builder,Circuit}.lean`,
//! leanerVM `532ebb4`, Apache-2.0; itself a transcription of leanVM `crates/flock/src/hash.rs`,
//! pin `a386121f`) with the chain step's constants.
//!
//! The gadget program is run once into a *tape*: a form (an `F₂`-linear combination of block
//! positions) is a node of an XOR DAG whose leaves are positions. One tape serves every use:
//! * the bit trace of a block (`trace`): the honest witness and its `Az`, `Bz` rows;
//! * the forward walk over `E` (`walk`, §2.4.2): `A0̃(r_k, r_j)`, `B0̃(r_k, r_j)`;
//! * the transpose walk over `E` (`transpose`): `Σ_k e_A(k) A0(k, ·) + e_B(k) B0(k, ·)`;
//! * the bitset rows (`row_bitsets`), for the known-answer dump of `rowOf`.
//!
//! Row conventions (`ProductCircuit.rowOf`): a gate position's row is its gate; the constant
//! position 512 has `(var 512, var 512)`; an input position `k` has `(var k, var 512)`; every
//! other position `(0, 0)`. In the chain R1CS, row 512 is replaced (§2.3) and `A0`, `B0` are the
//! matrices with row 512 removed: `walk` and `transpose` skip it (see the report, ambiguity A1).

use crate::blake2s::{IV, SIGMA};
use crate::field::E;

pub const BLOCK_LOG: usize = 14;
pub const BLOCK: usize = 1 << BLOCK_LOG;
pub const CPOS: usize = 512;
pub const MSG_IN: usize = 648; // the 256 free input bits (the digest being hashed)
pub const OUT: usize = 256;
pub const GATE_BASE: usize = 1280;

/// Node kinds. A node's value is a form; `Gate` is the variable of the gate's position.
#[derive(Clone, Copy, Debug)]
pub enum Node {
    Zero,
    Var(u32),
    Xor(u32, u32),
    /// The gate at position `p` with forms `a`, `b`; as a form it is `var p`.
    Gate(u32, u32, u32),
}

type Word = [u32; 32];

struct Builder {
    nodes: Vec<Node>,
    var_of: Vec<u32>, // position -> Var node (0 = none)
    next: usize,
    gates: Vec<(usize, u32, u32)>,
}

impl Builder {
    fn xor(&mut self, a: u32, b: u32) -> u32 {
        if a == 0 {
            return b;
        }
        if b == 0 {
            return a;
        }
        self.nodes.push(Node::Xor(a, b));
        (self.nodes.len() - 1) as u32
    }
    fn var(&mut self, p: usize) -> u32 {
        let p = p % BLOCK; // `pos` reduces modulo the block size
        if self.var_of[p] == 0 {
            self.nodes.push(Node::Var(p as u32));
            self.var_of[p] = (self.nodes.len() - 1) as u32;
        }
        self.var_of[p]
    }
    fn gate_at(&mut self, p: usize, a: u32, b: u32) -> u32 {
        self.nodes.push(Node::Gate(p as u32, a, b));
        self.gates.push((p, a, b));
        (self.nodes.len() - 1) as u32
    }
    /// `mul`: the gate `(a, b)` at the next position.
    fn mul(&mut self, a: u32, b: u32) -> u32 {
        let p = self.next;
        self.next += 1;
        self.gate_at(p % BLOCK, a, b)
    }
    fn xor_w(&mut self, x: &Word, y: &Word) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = self.xor(x[i], y[i]);
        }
        o
    }
    fn rotr_w(w: &Word, n: usize) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = w[(i + n) % 32];
        }
        o
    }
    fn lit_w(&mut self, c: u32) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            if (c >> i) & 1 == 1 {
                o[i] = self.var(CPOS);
            }
        }
        o
    }
    fn in_w(&mut self, b: usize) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            o[i] = self.var(b + i);
        }
        o
    }
    /// `addCarries x y 31 0`: carries `c_0 = 0, …, c_31`, one gate per carry into bits `1 … 31`.
    fn add_carries(&mut self, x: &Word, y: &Word) -> Vec<u32> {
        let mut cs = Vec::with_capacity(32);
        let mut c = 0;
        for i in 0..31 {
            let a = self.xor(x[i], c);
            let b = self.xor(y[i], c);
            let g = self.mul(a, b);
            cs.push(c);
            c = self.xor(c, g);
        }
        cs.push(c);
        cs
    }
    /// `sumW p q cs`: bit `i` is `p_i + q_i + c_i`.
    fn sum_w(&mut self, p: &Word, q: &Word, cs: &[u32]) -> Word {
        let mut o = [0; 32];
        for i in 0..32 {
            let pq = self.xor(p[i], q[i]);
            o[i] = self.xor(pq, cs.get(i).copied().unwrap_or(0));
        }
        o
    }
    fn add_w(&mut self, x: &Word, y: &Word) -> Word {
        let cs = self.add_carries(x, y);
        self.sum_w(x, y, &cs)
    }
    /// `add3W x y z`: 31 majority gates, then 30 ripple gates.
    fn add3_w(&mut self, x: &Word, y: &Word, z: &Word) -> Word {
        // majorities x y z 31
        let mut ms = Vec::with_capacity(31);
        for i in 0..31 {
            let a = self.xor(x[i], z[i]);
            let b = self.xor(y[i], z[i]);
            let g = self.mul(a, b);
            ms.push(self.xor(g, z[i]));
        }
        // xor3W x y z
        let mut p = [0; 32];
        for i in 0..32 {
            let xy = self.xor(x[i], y[i]);
            p[i] = self.xor(xy, z[i]);
        }
        // shiftW ms
        let mut q = [0; 32];
        for i in 1..32 {
            q[i] = ms[i - 1];
        }
        // rippleCarries p q 31 0
        let mut cs = Vec::with_capacity(32);
        let mut c = 0;
        for i in 0..31 {
            if i >= 1 {
                let a = self.xor(p[i], c);
                let b = self.xor(q[i], c);
                let g = self.mul(a, b);
                cs.push(c);
                c = self.xor(c, g);
            } else {
                cs.push(c);
            }
        }
        cs.push(c);
        self.sum_w(&p, &q, &cs)
    }
    #[allow(clippy::too_many_arguments)]
    fn g_w(&mut self, v: &mut [Word; 16], a: usize, b: usize, c: usize, d: usize, mx: &Word, my: &Word) {
        let a1 = self.add3_w(&v[a], &v[b], mx);
        let t = self.xor_w(&v[d], &a1);
        let d1 = Self::rotr_w(&t, 16);
        let c1 = self.add_w(&v[c], &d1);
        let t = self.xor_w(&v[b], &c1);
        let b1 = Self::rotr_w(&t, 12);
        let a2 = self.add3_w(&a1, &b1, my);
        let t = self.xor_w(&d1, &a2);
        let d2 = Self::rotr_w(&t, 8);
        let c2 = self.add_w(&c1, &d2);
        let t = self.xor_w(&b1, &c2);
        let b2 = Self::rotr_w(&t, 7);
        v[a] = a2;
        v[b] = b2;
        v[c] = c2;
        v[d] = d2;
    }
}

/// The chain block circuit as a tape plus the row of every position.
pub struct Circuit {
    pub nodes: Vec<Node>,
    /// `rows[k] = Some((a, b))`, or `None` for the zero row `(0, 0)`.
    pub rows: Vec<Option<(u32, u32)>>,
    /// The gates in evaluation order (`chainBlock.gates`): constant rows, compression gates,
    /// output rows.
    pub gates: Vec<(usize, u32, u32)>,
    pub v512: u32,
}

/// The constant bit of a constant position of the chain block, or `None` if `k` is not one
/// (§2.2.1): `h0` at 0…255, the tag `0x43` at 640…647, padding/zero message bytes at 904…1151,
/// counter `33` at 1152…1183, `t_hi` at 1184…1215, `f0 = 0xFFFFFFFF` at 1216…1247, `f1` at
/// 1248…1279.
pub fn const_bit(k: usize) -> Option<bool> {
    let h0 = crate::blake2s::h0();
    match k {
        0..=255 => Some((h0[k / 32] >> (k % 32)) & 1 == 1),
        640..=647 => Some((0x43u32 >> (k - 640)) & 1 == 1),
        904..=1151 => Some(false),
        1152..=1183 => Some((33u32 >> (k - 1152)) & 1 == 1),
        1184..=1215 => Some(false),
        1216..=1247 => Some(true),
        1248..=1279 => Some(false),
        _ => None,
    }
}

impl Circuit {
    /// `chainBlock`.
    pub fn build() -> Circuit {
        Self::build_variant(true)
    }

    /// `chainBlock` (`chain`), or leanerVM's `blake2sCircuit` itself (inputs `0…255` and
    /// `640…1279`, no constant rows), for the known-answer test against leanerVM's `rowsDigest`.
    pub fn build_variant(chain: bool) -> Circuit {
        let mut b = Builder { nodes: vec![Node::Zero], var_of: vec![0; BLOCK], next: GATE_BASE, gates: vec![] };
        let v512 = b.var(CPOS);
        // the constant rows, prepended to the gates (§2.2.1, revised after BP-M3), ascending
        // position: `(var 512, var 512)` where the bit is 1, `(0, 0)` where it is 0
        for k in 0..GATE_BASE {
            if !chain {
                break;
            }
            match const_bit(k) {
                Some(true) => {
                    b.gate_at(k, v512, v512);
                }
                Some(false) => {
                    b.gate_at(k, 0, 0);
                }
                None => {}
            }
        }
        // compressW
        let mut v: [Word; 16] = [[0; 32]; 16];
        for w in 0..16 {
            v[w] = if w < 8 {
                b.in_w(32 * w)
            } else if w < 12 {
                b.lit_w(IV[w - 8])
            } else {
                let l = b.lit_w(IV[w - 8]);
                let inp = b.in_w(1152 + 32 * (w - 12));
                b.xor_w(&l, &inp)
            };
        }
        let mut msg: [Word; 16] = [[0; 32]; 16];
        for w in 0..16 {
            msg[w] = b.in_w(640 + 32 * w);
        }
        for s in SIGMA.iter() {
            b.g_w(&mut v, 0, 4, 8, 12, &msg[s[0]], &msg[s[1]]);
            b.g_w(&mut v, 1, 5, 9, 13, &msg[s[2]], &msg[s[3]]);
            b.g_w(&mut v, 2, 6, 10, 14, &msg[s[4]], &msg[s[5]]);
            b.g_w(&mut v, 3, 7, 11, 15, &msg[s[6]], &msg[s[7]]);
            b.g_w(&mut v, 0, 5, 10, 15, &msg[s[8]], &msg[s[9]]);
            b.g_w(&mut v, 1, 6, 11, 12, &msg[s[10]], &msg[s[11]]);
            b.g_w(&mut v, 2, 7, 8, 13, &msg[s[12]], &msg[s[13]]);
            b.g_w(&mut v, 3, 4, 9, 14, &msg[s[14]], &msg[s[15]]);
        }
        assert_eq!(b.next, GATE_BASE + 14720, "80 G steps x 184 gates");
        let mut outs = [[0u32; 32]; 8];
        for w in 0..8 {
            let t = b.xor_w(&v[w], &v[w + 8]);
            let cv = b.in_w(32 * w);
            outs[w] = b.xor_w(&t, &cv);
        }
        // output rows (out bit, var 512)
        for w in 0..8 {
            for i in 0..32 {
                b.gate_at(OUT + 32 * w + i, outs[w][i], v512);
            }
        }
        // rows: gates first (first occurrence), then the constant, then inputs, else zero
        let mut rows: Vec<Option<(u32, u32)>> = vec![None; BLOCK];
        let mut is_gate = vec![false; BLOCK];
        for &(p, a, bb) in &b.gates {
            if !is_gate[p] {
                is_gate[p] = true;
                rows[p] = Some((a, bb));
            }
        }
        if !is_gate[CPOS] {
            rows[CPOS] = Some((v512, v512));
        }
        let inputs: Vec<usize> =
            if chain { (MSG_IN..MSG_IN + 256).collect() } else { (0..256).chain(640..1280).collect() };
        for k in inputs {
            if !is_gate[k] {
                let vk = b.var(k);
                rows[k] = Some((vk, v512));
            }
        }
        Circuit { nodes: b.nodes, rows, gates: b.gates, v512 }
    }

    /// The honest block for the message digest `d` (`chainTrace d`): returns the bits of the
    /// block `z` and of the rows' forms `Az`, `Bz` (each `2^14` bits as 256 words). Row 512 of
    /// the chain R1CS (`A = B = pub(0) = 1`) agrees with the constant row here.
    pub fn trace(&self, d: &[u8; 32], vals: &mut Vec<u8>) -> ([u64; 256], [u64; 256], [u64; 256]) {
        let mut z = vec![0u8; BLOCK];
        z[CPOS] = 1;
        for e in 0..32 {
            for bit in 0..8 {
                z[MSG_IN + 8 * e + bit] = (d[e] >> bit) & 1;
            }
        }
        vals.clear();
        vals.resize(self.nodes.len(), 0);
        for (i, nd) in self.nodes.iter().enumerate() {
            vals[i] = match *nd {
                Node::Zero => 0,
                Node::Var(p) => z[p as usize],
                Node::Xor(a, b) => vals[a as usize] ^ vals[b as usize],
                Node::Gate(p, a, b) => {
                    let v = vals[a as usize] & vals[b as usize];
                    z[p as usize] = v;
                    v
                }
            };
        }
        let mut zw = [0u64; 256];
        let mut aw = [0u64; 256];
        let mut bw = [0u64; 256];
        for k in 0..BLOCK {
            zw[k / 64] |= (z[k] as u64) << (k % 64);
            if let Some((a, b)) = self.rows[k] {
                aw[k / 64] |= (vals[a as usize] as u64) << (k % 64);
                bw[k / 64] |= (vals[b as usize] as u64) << (k % 64);
            }
        }
        (zw, aw, bw)
    }

    /// Node values over `E` with `var j ↦ wt(j)`.
    fn values(&self, wt: &[E]) -> Vec<E> {
        let mut val = vec![E::ZERO; self.nodes.len()];
        for (i, nd) in self.nodes.iter().enumerate() {
            val[i] = match *nd {
                Node::Zero => E::ZERO,
                Node::Var(p) | Node::Gate(p, _, _) => wt[p as usize],
                Node::Xor(a, b) => val[a as usize] + val[b as usize],
            };
        }
        val
    }

    /// The forward walk (§2.4.2): `(Σ_k e(k) Σ_j A0(k,j) wt(j), same for B0)` over the rows of the
    /// chain block, row 512 excluded when `skip512` (the chain R1CS's `A0`, `B0`), included when
    /// not (literal `rowOf`, for the known-answer dump).
    pub fn walk(&self, e: &[E], wt: &[E], skip512: bool) -> (E, E) {
        let val = self.values(wt);
        let mut a_acc = E::ZERO;
        let mut b_acc = E::ZERO;
        for k in 0..BLOCK {
            if skip512 && k == CPOS {
                continue;
            }
            if let Some((a, b)) = self.rows[k] {
                a_acc += e[k] * val[a as usize];
                b_acc += e[k] * val[b as usize];
            }
        }
        (a_acc, b_acc)
    }

    /// The transpose walk: `u(j) = Σ_{k ≠ 512} ea(k) A0(k, j) + eb(k) B0(k, j)`.
    pub fn transpose(&self, ea: &[E], eb: &[E]) -> Vec<E> {
        let mut adj = vec![E::ZERO; self.nodes.len()];
        for k in 0..BLOCK {
            if k == CPOS {
                continue;
            }
            if let Some((a, b)) = self.rows[k] {
                adj[a as usize] += ea[k];
                adj[b as usize] += eb[k];
            }
        }
        let mut u = vec![E::ZERO; BLOCK];
        for i in (1..self.nodes.len()).rev() {
            let g = adj[i];
            if g.is_zero() {
                continue;
            }
            match self.nodes[i] {
                Node::Zero => {}
                Node::Var(p) | Node::Gate(p, _, _) => u[p as usize] += g,
                Node::Xor(a, b) => {
                    adj[a as usize] += g;
                    adj[b as usize] += g;
                }
            }
        }
        u
    }

    /// The rows of `rowOf` as bitsets (`2^14` bits, 256 words each): `(a, b)` per position.
    pub fn row_bitsets(&self) -> Vec<([u64; 256], [u64; 256])> {
        let mut val: Vec<Box<[u64; 256]>> = Vec::with_capacity(self.nodes.len());
        for nd in self.nodes.iter() {
            let mut v = Box::new([0u64; 256]);
            match *nd {
                Node::Zero => {}
                Node::Var(p) | Node::Gate(p, _, _) => v[p as usize / 64] |= 1u64 << (p % 64),
                Node::Xor(a, b) => {
                    for w in 0..256 {
                        v[w] = val[a as usize][w] ^ val[b as usize][w];
                    }
                }
            }
            val.push(v);
        }
        (0..BLOCK)
            .map(|k| match self.rows[k] {
                Some((a, b)) => (*val[a as usize], *val[b as usize]),
                None => ([0u64; 256], [0u64; 256]),
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::blake2s::chain_step;
    use crate::mle::eq_table;

    #[test]
    fn trace_computes_chain_step_and_satisfies_rows() {
        let c = Circuit::build();
        let mut vals = vec![];
        for seed in 0..4u8 {
            let d: [u8; 32] = std::array::from_fn(|i| (i as u8).wrapping_mul(37).wrapping_add(seed.wrapping_mul(91)));
            let (z, a, b) = c.trace(&d, &mut vals);
            let out = chain_step(&d);
            for e in 0..32 {
                for bit in 0..8 {
                    let k = OUT + 8 * e + bit;
                    assert_eq!((z[k / 64] >> (k % 64)) & 1, ((out[e] >> bit) & 1) as u64);
                }
            }
            for w in 0..256 {
                assert_eq!(a[w] & b[w], z[w], "row word {w}");
            }
            // a flipped output bit violates its row
            let mut z2 = z;
            z2[OUT / 64] ^= 1;
            assert_ne!(a[OUT / 64] & b[OUT / 64], z2[OUT / 64]);
        }
    }

    /// leanerVM `tests/LeanerVMTests/Protocol/Blake2sCircuit.lean`: `rowsDigest blake2sCircuit ==
    /// 4056851438423586957`, the value its script computes from leanVM's Python verifier
    /// (`blake2s_row_values`, pin `a386121f`): `Σ_k (3 (A_k mod P) + 7 (B_k mod P)) (k + 1) mod P`,
    /// `P = 2^64 − 59`, a row read as the natural number `Σ_{j ∈ row} 2^j`.
    #[test]
    fn rows_digest_matches_leanervm() {
        let p: u128 = (1u128 << 64) - 59;
        let mut pow = vec![0u128; BLOCK];
        pow[0] = 1;
        for j in 1..BLOCK {
            pow[j] = pow[j - 1] * 2 % p;
        }
        let digest = |c: &Circuit| -> u128 {
            let rows = c.row_bitsets();
            let val = |v: &[u64; 256]| -> u128 {
                let mut acc = 0u128;
                for j in 0..BLOCK {
                    if (v[j / 64] >> (j % 64)) & 1 == 1 {
                        acc = (acc + pow[j]) % p;
                    }
                }
                acc
            };
            let mut d = 0u128;
            for k in 0..BLOCK {
                let (a, b) = &rows[k];
                d = (d + (val(a) * 3 + val(b) * 7) % p * (k as u128 + 1)) % p;
            }
            d
        };
        let plain = Circuit::build_variant(false);
        assert_eq!(plain.gates.len(), 14720 + 256);
        assert_eq!(digest(&plain), 4056851438423586957);
        // the chain block differs exactly on the input and constant rows
        assert_ne!(digest(&Circuit::build()), 4056851438423586957);
    }

    #[test]
    fn transpose_is_adjoint_of_walk() {
        let c = Circuit::build();
        let mut s = 99u64;
        let mut nx = || {
            s = s.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            s
        };
        let rk: Vec<E> = (0..14).map(|_| E([nx(), nx(), nx()])).collect();
        let rj: Vec<E> = (0..14).map(|_| E([nx(), nx(), nx()])).collect();
        let e = eq_table(&rk);
        let wt = eq_table(&rj);
        let (wa, wb) = c.walk(&e, &wt, true);
        let rho = E([nx(), nx(), nx()]);
        let eb: Vec<E> = e.iter().map(|&x| x * rho).collect();
        let u = c.transpose(&e, &eb);
        let mut dot = E::ZERO;
        for j in 0..BLOCK {
            dot += u[j] * wt[j];
        }
        assert_eq!(dot, wa + rho * wb);
    }
}
