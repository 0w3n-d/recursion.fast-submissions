#!/usr/bin/env python3
"""Planted bugs: each mutant is a copy of src/ with one deliberate fault (a wrong rotation, a wrong lane in
chi, a wrong round constant, padding byte or qword), regenerated where the fault is in a generator;
`test_keccak KERNEL` must fail on every one.  A mutant whose text does not occur exactly once (or, for a
generated file whose two functions share their round code, twice: the chain's copy is mutated) is an
error of this script, not a pass.  Kernels this CPU cannot run are skipped (and said so).

  test_mutants.py SRC_DIR [JOBS]
"""
import concurrent.futures
import os
import shutil
import subprocess
import sys
import tempfile

# (name, file, old, new, kernel, generator to rerun or None)
MUTANTS = [
    ('scalar: rho of lane 2', 'gen_scalar.py', 'RHO = [0,1,62,28,', 'RHO = [0,1,61,28,', 'scalar', 'gen_scalar.py'),
    ('scalar: chi lane', 'keccak_scalar.inc', 'r3_e11 = (r3_b11 ^ (r3_b12 & r3_b13));', 'r3_e11 = (r3_b11 ^ (r3_b12 & r3_b14));',
     'scalar', None),
    ('bmi: rho of lane 13', 'gen_lanes.py', '43, 25, 39,', '43, 24, 39,', 'bmi', 'gen_lanes.py'),
    ('bmi: chi lane', 'gen_lanes.py', 'b[(x + 2) % 5 + 5 * y], rc))', 'b[(x + 3) % 5 + 5 * y], rc))', 'bmi', 'gen_lanes.py'),
    ('bmi: padding byte', 'gen_lanes.py', "'h3 >> 56 | 0x100ull'", "'h3 >> 56 | 0x101ull'", 'bmi', 'gen_lanes.py'),
    ('avx512: rho of row 0', 'keccak_avx512.inc', 'rho0 = E512(0, 0, 0, 27, 28, 62, 1, 0)',
     'rho0 = E512(0, 0, 0, 27, 28, 61, 1, 0)', 'avx512', None),
    ('avx512: chi lane', 'keccak_avx512.inc', 'r1 = TL(n1, PM(rot1, n1), PM(rot2, n1), 0xD2);',
     'r1 = TL(n1, PM(rot2, n1), PM(rot1, n1), 0xD2);', 'avx512', None),
    ('avx512vl: rho of lane 21', 'gen_vlasm.py', '18, 2, 61, 56, 14]', '18, 3, 61, 56, 14]', 'avx512vl', 'gen_vlasm.py'),
    ('avx512vl: chi lane', 'gen_vlasm.py', "e('vpternlogq $0xD2, %s, %s, %s' % (x(r2), x(r1), x(b[j])))",
     "e('vpternlogq $0xD2, %s, %s, %s' % (x(r1), x(r2), x(b[j])))", 'avx512vl', 'gen_vlasm.py'),
    ('avx512vl: round constant 5', 'gen_vlasm.py', '0x000000000000808B, 0x0000000080000001, 0x8000000080008081',
     '0x000000000000808B, 0x0000000080000003, 0x8000000080008081', 'avx512vl', 'gen_vlasm.py'),
    ('avx512vl: second chain read from the first qword', 'gen_vlasm.py', 'memcpy(ob + 8 * i, &hv[i][1], 8)',
     'memcpy(ob + 8 * i, &hv[i][0], 8)', 'avx512vl', 'gen_vlasm.py'),
    ('avx512vln: chi lane (ANDN operands swapped)', 'gen_vlasm.py', "e('vpandnq %s, %s, %s' % (x(r2), x(r1), x(f[j])))",
     "e('vpandnq %s, %s, %s' % (x(r1), x(r2), x(f[j])))", 'avx512vln', 'gen_vlasm.py'),
    ('avx512vln: chi base lane', 'gen_vlasm.py', "e('vpxorq %s, %s, %s' % (x(b[j]), x(f[j]), x(f[j])))",
     "e('vpxorq %s, %s, %s' % (x(b[(j + 3) % 5]), x(f[j]), x(f[j])))", 'avx512vln', 'gen_vlasm.py'),
    ('avx512vln: second chain read from the first qword', 'gen_vlasm.py', 'memcpy(ob + 8 * i, &hv[i][1], 8)',
     'memcpy(ob + 8 * i, &hv[i][0], 8)', 'avx512vln', 'gen_vlasm.py'),
]
OUT = {'gen_scalar.py': 'keccak_scalar.inc', 'gen_lanes.py': 'keccak_lanes.inc', 'gen_vlasm.py': 'keccak_vlasm.inc'}


def one(src, m, available):
    name, fname, old, new, kernel, gen = m
    if kernel not in available:
        return name, 'skipped (this CPU cannot run %s)' % kernel, True
    d = tempfile.mkdtemp(prefix='mutant')
    try:
        for f in os.listdir(src):
            if os.path.isfile(os.path.join(src, f)):
                shutil.copy(os.path.join(src, f), d)
        text = open(os.path.join(d, fname)).read()
        n = text.count(old)
        if n not in ((1, 2) if fname.endswith('.inc') else (1,)):
            return name, 'ERROR: the text to mutate occurs %d times' % n, False
        i = text.rindex(old)                    # in a generated file, the last copy: the chain's
        open(os.path.join(d, fname), 'w').write(text[:i] + new + text[i + len(old):])
        if gen:
            with open(os.path.join(d, OUT[gen]), 'w') as f:
                subprocess.run([sys.executable, '-I', os.path.join(d, gen)], stdout=f, check=True)
        subprocess.run(['gcc', '-O2', '-w', '-o', os.path.join(d, 'tk'), os.path.join(d, 'test_keccak.c')], check=True)
        r = subprocess.run([os.path.join(d, 'tk'), kernel], capture_output=True, text=True, timeout=600)
        caught = r.returncode != 0
        line = next((l[l.index('FAIL'):] for l in r.stdout.splitlines() if 'FAIL:' in l), '')
        return name, ('caught: ' + line) if caught else 'NOT CAUGHT', caught
    finally:
        shutil.rmtree(d)


def main():
    src = os.path.abspath(sys.argv[1])
    jobs = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    tk = tempfile.mkdtemp(prefix='tk')
    subprocess.run(['gcc', '-O2', '-w', '-o', os.path.join(tk, 'tk'), os.path.join(src, 'test_keccak.c')], check=True)
    available = subprocess.run([os.path.join(tk, 'tk'), 'available'], capture_output=True, text=True).stdout.split()
    shutil.rmtree(tk)
    ok = True
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for name, what, good in ex.map(lambda m: one(src, m, available), MUTANTS):
            print('mutant %-50s %s' % (name, what))
            ok &= good
    print('all mutants caught' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


main()
