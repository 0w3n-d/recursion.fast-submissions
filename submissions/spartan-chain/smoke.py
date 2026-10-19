#!/usr/bin/env python3
"""The entry's smoke run (BASELINE-TASK §9's shape; adapted from submissions/baseline/smoke.py at
91b3a56), until S3's runner exists.

  smoke.py [--run ENTRY_RUN] [--prover PROVER] [--relation Relation.lean] [--r R] [--n N]
           [--target CARGO_TARGET_DIR] [--work DIR]

1. The native prover: `cargo build --release --offline` with CARGO_TARGET_DIR outside the root
   (default logs/spartan-chain/infra/target), unless --prover is given.
2. 2^r starts from os.urandom; `prover tree DIR` at (r, n) (default r = 2, n = 16), timed.
3. Leaf, node and root digests computed independently here (hashlib.blake2s; the tag bytes and
   `enc64` read from the contract's Relation.lean; the tree as Contract/Tree.lean's `treeRoot`).
4. The native verifier (`prover verify`) on the root and every inner proof against those digests
   (all accept), and the four canaries of DESIGN-v3 §6.3 step 7 on the first 8 proofs of each kind
   (one byte appended, the last byte removed, one statement bit flipped, a swapped child digest /
   a sibling's statement for a leaf): all reject. `prover node` on the root's children reproduces
   root.bin. Proof sizes match §7 (a node is 8·(11 + ⌈|π₁|/8⌉ + ⌈|π₂|/8⌉) bytes).
5. The compiled Lean verifier (`entry-verify verify`, built by check.sh outside the root:
   `vb (Leaf.leafVerifier chainEvals)` of SpartanChainVerifierTop and SpartanChainVerifier):
   * if its leaf verifier is the STUB (it says so on standard error), the n-step tree is only
     checked to be rejected at the leaves, and a second, zero-step tree (n = 0, which the stub
     decides exactly) is run through the Lean verifier: every proof accepted against the
     independent digests, every canary rejected, the native verifier agreeing on all of them;
   * otherwise the n-step tree is verified by the Lean verifier like the native one.
6. DoS sample: 16 random proofs of uniform length in [0, 2^20] under the root digest, both
   verifiers: all reject (maximum times reported).
A verdict is counted only with the verifier's own `Vb: accept`/`Vb: reject` line (Lean) or exit
code 0/1 (native; exit 2 is an error). Exit 0 iff every check passed.
"""
import argparse, hashlib, json, os, random, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.realpath(__file__))
REPO = os.path.realpath(os.path.join(HERE, "..", ".."))

def tags(relation):
    src = open(relation).read()
    t = {k: int(re.search(rf"def {k} : UInt8 := (0x[0-9A-Fa-f]+)", src).group(1), 16)
         for k in ("tagChain", "tagLeaf", "tagNode")}
    assert re.search(r"def enc64 \(n : ℕ\) : List UInt8 := List\.ofFn fun i : Fin 8 => "
                     r"\(n / 256 \^ i\.val\)\.toUInt8", src), "enc64 changed in Relation.lean"
    return {k: bytes([v]) for k, v in t.items()}

class Ref:
    """Independent digests (not the prover's code)."""
    def __init__(self, t):
        self.t = t
    def enc64(self, n):
        return bytes((n % 2 ** 64) >> (8 * i) & 0xFF for i in range(8))
    def leaf(self, s, n):
        h = s
        for _ in range(n):
            h = hashlib.blake2s(self.t["tagChain"] + h).digest()
        return hashlib.blake2s(self.t["tagLeaf"] + h + self.enc64(n)).digest()
    def node(self, c1, c2):
        return hashlib.blake2s(self.t["tagNode"] + c1 + c2).digest()
    def levels(self, leaves):
        lv = [leaves]
        while len(lv[-1]) > 1:
            cs = lv[-1]
            lv.append([self.node(cs[i], cs[i + 1]) for i in range(0, len(cs) - 1, 2)] + cs[len(cs) - len(cs) % 2:])
        return lv

class Verifier:
    """One verifier binary; `lean` verdicts need the verifier's own Vb line."""
    def __init__(self, cmd, work, lean):
        self.cmd, self.work, self.lean, self.k, self.max, self.stub = cmd, work, lean, 0, 0.0, None
    def __call__(self, stmt, proof):
        self.k += 1
        sp, pp = os.path.join(self.work, f"v{self.k}.stmt"), os.path.join(self.work, f"v{self.k}.bin")
        open(sp, "w").write(stmt.hex()); open(pp, "wb").write(proof)
        t0 = time.monotonic()
        r = subprocess.run(self.cmd + ["verify", sp, pp], capture_output=True, text=True)
        dt = time.monotonic() - t0
        self.max = max(self.max, dt)
        os.remove(sp); os.remove(pp)
        if self.lean:
            self.stub = "leaf verifier: STUB" in r.stderr
            verdict = {0: "Vb: accept", 1: "Vb: reject"}.get(r.returncode)
            if verdict is None or verdict not in r.stderr:
                raise SystemExit(f"Lean verify crashed (exit {r.returncode}): {r.stderr.strip()}")
        elif r.returncode not in (0, 1):
            raise SystemExit(f"native verify failed (exit {r.returncode}): {r.stderr.strip()}")
        return r.returncode == 0, dt

def tree(prover, ref, r, n, work):
    os.makedirs(work, exist_ok=True)
    starts = [os.urandom(32) for _ in range(2 ** r)]
    json.dump({"n": n, "starts": [s.hex() for s in starts]}, open(os.path.join(work, "leaves.json"), "w"))
    t0 = time.monotonic()
    subprocess.run(prover + ["tree", work], check=True, capture_output=True)
    dt = time.monotonic() - t0
    lv = ref.levels([ref.leaf(s, n) for s in starts])
    rd = lambda p: open(os.path.join(work, p), "rb").read()
    proofs = {(0, i): rd(f"proofs/L{i}.bin") for i in range(2 ** r)}
    proofs.update({(k, j): rd(f"proofs/N{k}_{j}.bin") for k in range(1, r + 1) for j in range(2 ** (r - k))})
    return lv, proofs, rd("root.bin"), dt

def canaries(lv, proofs, r):
    """(name, kind, statement, proof) for the four canary kinds on the first 8 proofs of each kind."""
    out = []
    for kind, keys in (("leaf", [(0, i) for i in range(2 ** r)][:8]),
                       ("node", [(k, j) for k in range(1, r + 1) for j in range(2 ** (r - k))][:8])):
        for k, j in keys:
            p, c = proofs[(k, j)], lv[k][j]
            flipped = bytes([c[0] ^ 1]) + c[1:]
            swapped = lv[0][j ^ 1] if k == 0 else Ref.node(REF, lv[k - 1][2 * j + 1], lv[k - 1][2 * j])
            for name, stmt, proof in (("appended byte", c, p + b"\0"), ("last byte removed", c, p[:-1]),
                                      ("statement bit flipped", flipped, p), ("swapped child digest", swapped, p)):
                out.append((f"{kind} {k}/{j} {name}", stmt, proof))
    return out

REF = None

def main():
    global REF
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", default=os.path.join(os.environ.get("CORE") or os.path.join(REPO, "logs/spartan-chain/infra/core"),
                                                  ".lake/build/bin/entry-verify"))
    ap.add_argument("--prover")
    ap.add_argument("--target", default=os.path.join(REPO, "logs/spartan-chain/infra/target"))
    ap.add_argument("--relation", default=os.path.join(REPO, ".contract/RecursionFast/Contract/Relation.lean"))
    ap.add_argument("--r", type=int, default=2)
    ap.add_argument("--n", type=int, default=16)
    ap.add_argument("--work")
    a = ap.parse_args()
    work = a.work or tempfile.mkdtemp(prefix="spartan-smoke-")
    os.makedirs(work, exist_ok=True)
    fails = []
    def check(ok, what):
        print(("ok    " if ok else "FAIL  ") + what)
        if not ok:
            fails.append(what)

    if a.prover:
        prover = [a.prover]
    else:
        t0 = time.monotonic()
        subprocess.run(["cargo", "build", "--release", "--offline", "--manifest-path", os.path.join(HERE, "Cargo.toml")],
                       check=True, env=dict(os.environ, CARGO_TARGET_DIR=a.target))
        prover = [os.path.join(a.target, "release", "spartan-chain-prover")]
        print(f"cargo build --release: {time.monotonic() - t0:.1f} s wall")
    run = os.path.realpath(a.run)
    if not os.access(run, os.X_OK):
        raise SystemExit(f"no executable {run}: run check.sh first (it builds entry-verify)")
    REF = Ref(tags(a.relation))
    native, lean = Verifier(prover, work, False), Verifier([run], work, True)
    print(f"r = {a.r}, n = {a.n}, work {work}, prover {prover[0]}, Lean verifier {run}")

    def full(vfy, label, lv, proofs, root_bin, r):
        root = lv[-1][0]
        ok, dt = vfy(root, root_bin)
        check(ok, f"{label}: root check ({len(root_bin)} B, {dt:.3f} s)")
        for (k, j), p in sorted(proofs.items()):
            ok, _ = vfy(lv[k][j], p)
            check(ok, f"{label}: {'L' if k == 0 else 'N%d_' % k}{j} accepted against its independent digest")
        for name, stmt, proof in canaries(lv, proofs, r):
            ok, _ = vfy(stmt, proof)
            check(not ok, f"{label}: canary {name} rejected")

    lv, proofs, root_bin, dt = tree(prover, REF, a.r, a.n, os.path.join(work, "tree"))
    print(f"prover tree (r = {a.r}, n = {a.n}): {dt:.2f} s wall, root {len(root_bin)} B")
    check(root_bin == proofs[(a.r, 0)], "root.bin is the top node's proof")
    pad = lambda x: x + (-x % 8)
    for k in range(1, a.r + 1):
        for j in range(2 ** (a.r - k)):
            exp = 8 * (11 + pad(len(proofs[(k - 1, 2 * j)])) // 8 + pad(len(proofs[(k - 1, 2 * j + 1)])) // 8)
            check(len(proofs[(k, j)]) == exp, f"node {k}/{j} size {len(proofs[(k, j)])} = 8·(11 + ⌈|π₁|/8⌉ + ⌈|π₂|/8⌉)")
    full(native, "native", lv, proofs, root_bin, a.r)
    nd = os.path.join(work, "node")
    os.makedirs(nd)
    for i in (1, 2):
        open(os.path.join(nd, f"child{i}.stmt"), "w").write(lv[a.r - 1][i - 1].hex())
        open(os.path.join(nd, f"child{i}.proof"), "wb").write(proofs[(a.r - 1, i - 1)])
    subprocess.run(prover + ["node", nd], check=True, capture_output=True)
    check(open(os.path.join(nd, "proof.bin"), "rb").read() == root_bin, "prover node on the root's children reproduces root.bin")

    ok, _ = lean(lv[0][0], proofs[(0, 0)])
    if lean.stub:
        print("Lean verifier: the leaf verifier is the STUB; the n-step tree is checked natively only")
        check(a.n == 0 or not ok, "Lean (stub): an n-step leaf is rejected")
        lv0, proofs0, root0, dt0 = tree(prover, REF, a.r, 0, os.path.join(work, "tree0"))
        print(f"prover tree (r = {a.r}, n = 0): {dt0:.2f} s wall, root {len(root0)} B")
        check(all(len(proofs0[(0, i)]) == 80 for i in range(2 ** a.r)), "zero-step leaf proofs are 80 bytes")
        full(lean, "Lean (n = 0)", lv0, proofs0, root0, a.r)
        full(native, "native (n = 0)", lv0, proofs0, root0, a.r)
    else:
        full(lean, "Lean", lv, proofs, root_bin, a.r)

    root = lv[-1][0]
    for vfy, label in ((lean, "Lean"), (native, "native")):
        vfy.max = 0.0
        for i in range(16):
            ok, _ = vfy(root, os.urandom(random.randint(0, 2 ** 20)))
            check(not ok, f"DoS {label} random proof {i} rejected")
        print(f"DoS sample ({label}): max {vfy.max:.3f} s process wall over 16 random proofs")
    if not a.work:
        shutil.rmtree(work)
    print(f"SMOKE: {'FAIL (' + str(len(fails)) + ')' if fails else 'OK'}")
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main())
