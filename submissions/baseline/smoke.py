#!/usr/bin/env python3
"""The baseline's smoke run and calibration (BASELINE-TASK §9), until S3's runner replaces them.

  smoke.py [--run BASELINE_RUN] [--relation Relation.lean] [--r R] [--n N] [--work DIR]
  smoke.py --calibrate [--run ...] [--r 8] [--n 16384] [--repeat 3] [--work DIR]

Smoke (default r = 2, n = 16):
  1. 2^r starts from os.urandom; `prover.py tree DIR` (the native prover).
  2. Leaf, node and root digests computed independently here, with hashlib.blake2s and the tag
     bytes read from the contract's Relation.lean (`tagChain`, `tagLeaf`, `tagNode`; `enc64` is
     the 8 little-endian bytes of n mod 2^64), the tree as Contract/Tree.lean's `treeRoot`.
  3. The compiled verifier (`baseline-run verify`, the certified `Challenge.submission`'s `Vb`) on
     the root and on every inner proof, against those digests: all must accept.
  4. The four canaries of DESIGN-v3 §6.3 step 7 on the first 8 proofs of each kind (leaf, node):
     one byte appended, the last byte removed, one statement bit flipped, a swapped child digest
     (a node under `nodeStmt c2 c1`; a leaf under its sibling's digest): all must reject.
  5. `prover.py node DIR` on the root's two children: the proof equals root.bin and is accepted.
     The proof sizes match the format (leaf 48 bytes, node 88 + pad8 + pad8).
  6. The compiled Lean prover `P` (`baseline-run prove-leaf`/`prove-node`) writes the same bytes as
     the native prover on one leaf and one node, and the native encoder reproduces the
     kernel-checked known answers of BaselineV3Controls (`encode_leaf_kat`, `encode_node_kat`).
  7. DoS sample: 16 random proofs of uniform length in [0, 2^20] under the root digest, and three
     adversarially shaped 2^20-byte proofs (tag word 0 or 1, and a node with consistent lengths):
     all must reject; the maximum times are reported.
Calibration (DESIGN-v3 §6.5): the native prover on 2^r chains of n steps, then the compiled `Vb` on
the root, `--repeat` times; the machine description (CPU model, cores, flags, load) is printed.
Exit 0 iff every check passed.
"""
import argparse, hashlib, importlib.util, json, os, random, re, shutil, subprocess, sys, tempfile, time

HERE = os.path.dirname(os.path.realpath(__file__))
REPO = os.path.realpath(os.path.join(HERE, "..", ".."))

def load_prover():
    sys.dont_write_bytecode = True      # keep the root flat: no __pycache__
    spec = importlib.util.spec_from_file_location("baseline_prover", os.path.join(HERE, "prover.py"))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m

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
        """treeRoot's levels: adjacent pairs, an odd last digest carried up."""
        lv = [leaves]
        while len(lv[-1]) > 1:
            cs = lv[-1]
            lv.append([self.node(cs[i], cs[i + 1]) for i in range(0, len(cs) - 1, 2)] + cs[len(cs) - len(cs) % 2:])
        return lv

class Verifier:
    def __init__(self, run, work):
        self.run, self.work, self.k, self.max = run, work, 0, 0.0
    def __call__(self, stmt, proof):
        self.k += 1
        sp, pp = os.path.join(self.work, f"v{self.k}.stmt"), os.path.join(self.work, f"v{self.k}.bin")
        open(sp, "w").write(stmt.hex()); open(pp, "wb").write(proof)
        t0 = time.monotonic()
        r = subprocess.run([self.run, "verify", sp, pp], capture_output=True, text=True)
        dt = time.monotonic() - t0
        self.max = max(self.max, dt)
        os.remove(sp); os.remove(pp)
        verdict = {0: "Vb: accept", 1: "Vb: reject"}.get(r.returncode)
        if verdict is None or verdict not in r.stderr:
            raise SystemExit(f"verify crashed (exit {r.returncode}): {r.stderr.strip()}")
        return r.returncode == 0, dt, r.stderr.strip()

def machine():
    cpu = open("/proc/cpuinfo").read()
    model = re.search(r"model name\s*:\s*(.*)", cpu).group(1)
    flags = set(re.search(r"flags\s*:\s*(.*)", cpu).group(1).split())
    return (f"machine: {model}; {os.cpu_count()} logical CPUs; pclmulqdq {'pclmulqdq' in flags}, "
            f"vpclmulqdq {'vpclmulqdq' in flags}, gfni {'gfni' in flags}, avx2 {'avx2' in flags}, "
            f"sha_ni {'sha_ni' in flags}; load average {open('/proc/loadavg').read().split()[:3]}")

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--run", default=os.path.join(os.environ.get("CORE") or os.path.join(REPO, "logs/V3-S2/core-interim"),
                                                  ".lake/build/bin/entry-run"))
    ap.add_argument("--relation", default=os.path.join(REPO, ".contract/RecursionFast/Contract/Relation.lean"))
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--r", type=int)
    ap.add_argument("--n", type=int)
    ap.add_argument("--repeat", type=int, default=3)
    ap.add_argument("--work")
    a = ap.parse_args()
    r = a.r if a.r is not None else (8 if a.calibrate else 2)
    n = a.n if a.n is not None else (2 ** 14 if a.calibrate else 16)
    run = os.path.realpath(a.run)
    if not os.access(run, os.X_OK):
        raise SystemExit(f"no executable {run}: run check.sh (or the core branch's scripts/setup-scratch.sh) first")
    work = a.work or tempfile.mkdtemp(prefix="baseline-smoke-")
    os.makedirs(work, exist_ok=True)
    ref, prover, verify = Ref(tags(a.relation)), load_prover(), Verifier(run, work)
    fails = []
    def check(ok, what):
        print(("ok    " if ok else "FAIL  ") + what)
        if not ok:
            fails.append(what)

    print(machine())
    print(f"r = {r}, n = {n}, work {work}, verifier {run}")
    starts = [os.urandom(32) for _ in range(2 ** r)]
    json.dump({"n": n, "starts": [s.hex() for s in starts]}, open(os.path.join(work, "leaves.json"), "w"))
    t0 = time.monotonic()
    subprocess.run([sys.executable, "-I", os.path.join(HERE, "prover.py"), "tree", work], check=True)
    print(f"prover tree: {time.monotonic() - t0:.2f} s wall")
    rd = lambda p: open(os.path.join(work, p), "rb").read()
    t0 = time.monotonic()
    lv = ref.levels([ref.leaf(s, n) for s in starts])
    print(f"independent digests: {time.monotonic() - t0:.2f} s wall")
    root = lv[-1][0]

    if a.calibrate:
        print(f"root proof: {len(rd('root.bin'))} bytes")
        for i in range(a.repeat):
            ok, dt, msg = verify(root, rd("root.bin"))
            check(ok, f"root check {i + 1}: {dt:.3f} s process wall; {msg}")
        return finish(fails, work, a.work)

    proofs = {(0, i): rd(f"proofs/L{i}.bin") for i in range(2 ** r)}
    proofs.update({(k, j): rd(f"proofs/N{k}_{j}.bin") for k in range(1, r + 1) for j in range(2 ** (r - k))})
    check(rd("root.bin") == proofs[(r, 0)], "root.bin is the top node's proof")
    ok, dt, msg = verify(root, rd("root.bin"))
    check(ok, f"root check: {msg}")
    for (k, j), p in sorted(proofs.items()):
        ok, dt, msg = verify(lv[k][j], p)
        check(ok, f"{'L' if k == 0 else 'N%d_' % k}{j} accepted against its independent digest: {msg}")
    pad = lambda x: x + (-x % 8)
    sizes = [48]
    for k in range(1, r + 1):
        sizes.append(88 + 2 * pad(sizes[-1]))
    check(all(len(p) == sizes[k] for (k, _), p in proofs.items()), f"proof sizes by level {sizes}")

    for kind, keys in (("leaf", [(0, i) for i in range(2 ** r)][:8]),
                       ("node", [(k, j) for k in range(1, r + 1) for j in range(2 ** (r - k))][:8])):
        for k, j in keys:
            p, c = proofs[(k, j)], lv[k][j]
            flipped = bytes([c[0] ^ 1]) + c[1:]
            if k == 0:
                swapped = lv[0][j ^ 1]
            else:
                swapped = ref.node(lv[k - 1][2 * j + 1], lv[k - 1][2 * j])
            for name, (stmt, proof) in (("appended byte", (c, p + b"\0")), ("last byte removed", (c, p[:-1])),
                                        ("statement bit flipped", (flipped, p)), ("swapped child digest", (swapped, p))):
                ok, dt, msg = verify(stmt, proof)
                check(not ok, f"canary {kind} {k}/{j} {name}: {msg}")

    nd = os.path.join(work, "node")
    os.makedirs(nd)
    for i in (1, 2):
        open(os.path.join(nd, f"child{i}.stmt"), "w").write(lv[r - 1][i - 1].hex())
        open(os.path.join(nd, f"child{i}.proof"), "wb").write(proofs[(r - 1, i - 1)])
    subprocess.run([sys.executable, "-I", os.path.join(HERE, "prover.py"), "node", nd], check=True)
    np_ = open(os.path.join(nd, "proof.bin"), "rb").read()
    check(np_ == rd("root.bin"), "prover node on the root's children reproduces root.bin")
    ok, dt, msg = verify(root, np_)
    check(ok, f"node-mode proof accepted: {msg}")

    lp = os.path.join(work, "lean")
    os.makedirs(lp)
    open(os.path.join(lp, "s.hex"), "w").write(starts[0].hex())
    subprocess.run([run, "prove-leaf", os.path.join(lp, "s.hex"), str(n), os.path.join(lp, "L0.bin")], check=True)
    check(open(os.path.join(lp, "L0.bin"), "rb").read() == proofs[(0, 0)], "Lean P on leaf 0 = native prover")
    open(os.path.join(lp, "c1.hex"), "w").write(lv[0][0].hex())
    open(os.path.join(lp, "c2.hex"), "w").write(lv[0][1].hex())
    subprocess.run([run, "prove-node", os.path.join(lp, "c1.hex"), os.path.join(lp, "c2.hex"),
                    os.path.join(work, "proofs/L0.bin"), os.path.join(work, "proofs/L1.bin"),
                    os.path.join(lp, "N.bin")], check=True)
    check(open(os.path.join(lp, "N.bin"), "rb").read() == proofs[(1, 0)], "Lean P on node 1/0 = native prover")
    kat_leaf = bytes(8) + bytes([1] * 32) + bytes([16]) + bytes(7)
    kat_node = (bytes([1]) + bytes(7) + bytes([2] * 32) + bytes([3] * 32) + bytes([3]) + bytes(7)
                + bytes([0xaa, 0xbb, 0xcc]) + bytes(5) + bytes([1]) + bytes(7) + bytes([0xdd]) + bytes(7))
    check(prover.enc_leaf(bytes([1] * 32), 16) == kat_leaf, "native encoder = encode_leaf_kat")
    check(prover.enc_node(bytes([2] * 32), bytes([3] * 32), bytes([0xaa, 0xbb, 0xcc]), bytes([0xdd])) == kat_node,
          "native encoder = encode_node_kat")

    verify.max = 0.0
    for i in range(16):
        ok, dt, msg = verify(root, os.urandom(random.randint(0, 2 ** 20)))
        check(not ok, f"DoS random proof {i}: {msg}")
    print(f"DoS sample: max {verify.max:.3f} s process wall over 16 random proofs")
    verify.max = 0.0
    u64 = lambda x: x.to_bytes(8, "little")
    h = 2 ** 19
    shaped = {"tag 0, random rest": u64(0) + os.urandom(2 ** 20 - 8),
              "tag 1, random rest": u64(1) + os.urandom(2 ** 20 - 8),
              "tag 1, consistent lengths": u64(1) + os.urandom(64) + u64(h) + os.urandom(h)
                                           + u64(h - 96) + os.urandom(h - 96)}
    for name, p in shaped.items():
        ok, dt, msg = verify(root, p)
        check(not ok, f"adversarial 1 MiB proof ({name}): {msg}")
    print(f"adversarial shapes: max {verify.max:.3f} s process wall over {len(shaped)} proofs")
    return finish(fails, work, a.work)

def finish(fails, work, keep):
    if not keep:
        shutil.rmtree(work)
    print(f"SMOKE: {'FAIL (' + str(len(fails)) + ')' if fails else 'OK'}")
    return 1 if fails else 0

if __name__ == "__main__":
    sys.exit(main())
