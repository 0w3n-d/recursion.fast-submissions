#!/usr/bin/env python3
"""The known-answer harness of BLUEPRINT-R1 §11.3: run the Rust prover's `dump-*` commands and the
Lean side's dumps (`SpartanChainKat.lean`, through a driver outside the entry root), then diff them
file by file. Exit 0 iff every compared dump is identical.

  kat.py --rust BIN --lean-dir CLONE [--out DIR] [--lean-exe EXE] [NAME ...]

  BIN        the built `spartan-chain-prover`
  CLONE      a Lean clone whose lakefile has the entry's modules and the driver
             `scratch/kat/KatMain.lean` (the shared development clone `rf-core-sc`)
  --lean-exe a compiled driver; default: `lake env lean --run scratch/kat/KatMain.lean` in CLONE
             (the interpreter; see the report, §KAT, for why not the compiled executable)
  NAME       field mle transcript-ops encode phi sumcheck walk circuit leaf (default: all)

Formats: docs/snark-baseline/reports/rust-prover.md §5. `leaf` compares the Lean recomputation
(from the Rust prover's challenges and tables of the n = 1 KAT leaf, `leaf-input.txt`) with the
values in the Rust proof (`leaf-expect.txt`).
"""
import argparse, os, subprocess, sys, time

NAMES = ["field", "mle", "transcript-ops", "encode", "phi", "sumcheck", "walk", "circuit", "leaf"]


def run(cmd, cwd=None, out=None):
    t = time.time()
    with open(out, "wb") if out else open(os.devnull, "wb") as f:
        r = subprocess.run(cmd, cwd=cwd, stdout=f, stderr=subprocess.PIPE)
    if r.returncode != 0:
        raise SystemExit(f"{' '.join(cmd)}: exit {r.returncode}\n{r.stderr.decode(errors='replace')[-2000:]}")
    return time.time() - t


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--rust", required=True)
    ap.add_argument("--lean-dir", required=True)
    ap.add_argument("--lean-exe")
    ap.add_argument("--out", default="kat-out")
    ap.add_argument("names", nargs="*")
    a = ap.parse_args()
    names = a.names or NAMES
    rdir, ldir = os.path.abspath(os.path.join(a.out, "rust")), os.path.abspath(os.path.join(a.out, "lean"))
    os.makedirs(rdir, exist_ok=True)
    os.makedirs(ldir, exist_ok=True)
    lean = [a.lean_exe] if a.lean_exe else ["lake", "env", "lean", "--run", "scratch/kat/KatMain.lean"]
    bad = []
    for n in names:
        if n == "leaf":
            tr = run([a.rust, "dump-leaf-trace", rdir])
            rfile = os.path.join(rdir, "leaf-expect.txt")
            tl = run(lean + [ldir, "--leaf", os.path.join(rdir, "leaf-input.txt")], cwd=a.lean_dir)
        else:
            rfile = os.path.join(rdir, f"{n}.txt")
            tr = run([a.rust, f"dump-{n}"], out=rfile)
            tl = run(lean + [ldir, n], cwd=a.lean_dir)
        lfile = os.path.join(ldir, f"{n}.txt")
        rl, ll = open(rfile).read().splitlines(), open(lfile).read().splitlines()
        diffs = [(i, x, y) for i, (x, y) in enumerate(zip(rl, ll)) if x != y]
        if len(rl) != len(ll):
            diffs.append((min(len(rl), len(ll)), f"<{len(rl)} lines>", f"<{len(ll)} lines>"))
        status = "SAME" if not diffs else f"DIFF ({len(diffs)} lines)"
        print(f"{n:15} {len(rl):6} lines  rust {tr:7.2f}s  lean {tl:7.2f}s  {status}", flush=True)
        for i, x, y in diffs[:5]:
            print(f"    line {i + 1}\n      rust: {x[:200]}\n      lean: {y[:200]}")
        if diffs:
            bad.append(n)
    print("KAT: PASS" if not bad else f"KAT: FAIL ({', '.join(bad)})")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
