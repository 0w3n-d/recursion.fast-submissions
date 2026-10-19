#!/usr/bin/env python3
"""The baseline's native prover (DESIGN-v3 §6.3): witness sending. Dependency-free (python3 and its
standard library's hashlib.blake2s). It is never proved; its proofs are checked by the compiled
verifier (`BaselineV3Run`'s `verify`, `smoke.py`).

  prover.py tree DIR    reads DIR/leaves.json {"n": N, "starts": [64 hex digits, ...]} (2^r starts),
                        writes DIR/proofs/L<i>.bin (leaf i), DIR/proofs/N<level>_<j>.bin (node j of
                        level 1 .. r, level r the root) and DIR/root.bin (the root's proof)
  prover.py node DIR    reads DIR/child1.stmt, DIR/child1.proof, DIR/child2.stmt, DIR/child2.proof
                        (a statement: 64 hex digits, or 32 raw bytes), writes DIR/proof.bin

S3 fixes the file formats (AGENTS.md §7); these are the ones `smoke.py` uses.

Byte format: the core library's `encode` (RecursionFast.Library.WitnessSending, the bytes of the
extractor output words `witWords`, Library/Words.lean); u64 is 8 little-endian bytes:
  leaf (s, n)              u64(0) || s || u64(n)                                   (48 bytes)
  node (c1, c2, p1, p2)    u64(1) || c1 || c2 || u64(|p1|) || p1 || 0^pad(|p1|)
                                             || u64(|p2|) || p2 || 0^pad(|p2|)     (pad to 8 bytes)
Hashes (RecursionFast/Contract/Relation.lean): chainStep d = BLAKE2s-256(0x43 || d) applied n
times from the start; leafStmt h n = BLAKE2s-256(0x4C || h || u64(n)); nodeStmt c1 c2 =
BLAKE2s-256(0x4E || c1 || c2); the tree pairs adjacent digests level by level (Contract/Tree.lean).
"""
import hashlib, json, os, sys
from concurrent.futures import ProcessPoolExecutor

TAG_CHAIN, TAG_LEAF, TAG_NODE = b"\x43", b"\x4c", b"\x4e"
CHAIN_CAP = 2 ** 20

def u64(n):
    return n.to_bytes(8, "little")

def pad8(b):
    return b + bytes(-len(b) % 8)

def chain_end(s, n):
    h = s
    for _ in range(n):
        h = hashlib.blake2s(TAG_CHAIN + h).digest()
    return h

def leaf_stmt(h, n):
    return hashlib.blake2s(TAG_LEAF + h + u64(n)).digest()

def node_stmt(c1, c2):
    return hashlib.blake2s(TAG_NODE + c1 + c2).digest()

def enc_leaf(s, n):
    return u64(0) + s + u64(n)

def enc_node(c1, c2, p1, p2):
    return u64(1) + c1 + c2 + u64(len(p1)) + pad8(p1) + u64(len(p2)) + pad8(p2)

def leaf(args):
    s, n = args
    return leaf_stmt(chain_end(s, n), n), enc_leaf(s, n)

def read_stmt(path):
    b = open(path, "rb").read()
    if len(b) == 32:
        return b
    h = b.decode("ascii").strip()
    if len(h) != 64:
        raise SystemExit(f"{path}: not a statement (64 hex digits or 32 bytes)")
    return bytes.fromhex(h)

def tree(d):
    spec = json.load(open(os.path.join(d, "leaves.json")))
    n, starts = spec["n"], [bytes.fromhex(s) for s in spec["starts"]]
    if not (0 <= n <= CHAIN_CAP) or not starts or len(starts) & (len(starts) - 1) or any(len(s) != 32 for s in starts):
        raise SystemExit("leaves.json: n in [0, 2^20], a power of two of 32-byte starts")
    os.makedirs(os.path.join(d, "proofs"), exist_ok=True)
    with ProcessPoolExecutor(min(len(starts), os.cpu_count() or 1)) as ex:
        level = list(ex.map(leaf, [(s, n) for s in starts]))
    for i, (_, p) in enumerate(level):
        open(os.path.join(d, "proofs", f"L{i}.bin"), "wb").write(p)
    k = 0
    while len(level) > 1:
        k += 1
        level = [(node_stmt(c1, c2), enc_node(c1, c2, p1, p2))
                 for (c1, p1), (c2, p2) in zip(level[0::2], level[1::2])]
        for j, (_, p) in enumerate(level):
            open(os.path.join(d, "proofs", f"N{k}_{j}.bin"), "wb").write(p)
    open(os.path.join(d, "root.bin"), "wb").write(level[0][1])

def node(d):
    f = lambda x: os.path.join(d, x)
    p = enc_node(read_stmt(f("child1.stmt")), read_stmt(f("child2.stmt")),
                 open(f("child1.proof"), "rb").read(), open(f("child2.proof"), "rb").read())
    open(f("proof.bin"), "wb").write(p)

if __name__ == "__main__":
    if len(sys.argv) != 3 or sys.argv[1] not in ("tree", "node"):
        raise SystemExit("usage: prover.py tree DIR | prover.py node DIR")
    (tree if sys.argv[1] == "tree" else node)(sys.argv[2])
