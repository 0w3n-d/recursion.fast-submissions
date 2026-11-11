#!/usr/bin/env python3
"""Offline test of the prover against the reference prover (src/ref_prover.c), through a strict fake
oracle service, for every kernel this CPU runs and for every way a request chooses its kernel.

  test_prover.py REFERENCE FAST "KERNELS"      KERNELS: the names `test_keccak available` prints

FAST may be a command with arguments ("qemu-x86_64 -cpu Haswell PROVER"); TP_QUICK=1 keeps the chains
short (for emulators).

The fake service (one per stream and prover) checks every request header, answers each SIGN with its own
signature and index (counting up from 0x9ABC0000, so that a wrong widening of the 32-bit index shows),
and sends each reply in 700-byte pieces.  Both provers make the same SIGNs in the same order, so their
files of the same stream are equal byte for byte, signatures included; the last signature of each file
is also checked against the one the fake sent.  Also covered: `prover setup`, the setup file missing or
naming an unusable kernel, RF_KECCAK naming an unusable kernel, a refused SIGN and a truncated prev.bin."""
import json
import os
import shutil
import socket
import struct
import subprocess
import sys
import tempfile
import threading
import time

SIG_BYTES = 4768                     # 133 x 32 one-time signature + 16 x 32 Merkle path
IDX0 = 0x9ABC0000


class Fake:
    """mode 'ok': a distinct signature per SIGN; 'refuse': status 3 to the first SIGN."""

    def __init__(self, path, mode='ok'):
        self.mode, self.signs, self.bad, self.sent = mode, 0, [], []
        self.lock = threading.Lock()
        self.srv = socket.socket(socket.AF_UNIX)
        self.srv.bind(path)
        self.srv.listen(8)
        threading.Thread(target=self.accept, daemon=True).start()

    def accept(self):
        while True:
            c, _ = self.srv.accept()
            threading.Thread(target=self.serve, args=(c,), daemon=True).start()

    def serve(self, c):
        def rd(n):
            b = b''
            while len(b) < n:
                k = c.recv(n - len(b))
                if not k:
                    raise EOFError
                b += k
            return b
        try:
            while True:
                h = rd(16)
                if struct.unpack('<B3sIQ', h) != (2, b'\0\0\0', 0, 0):     # SIGN, no item, no body
                    self.bad.append(h)
                    return
                with self.lock:
                    i = self.signs
                    self.signs += 1
                if self.mode == 'refuse':
                    m = b'exhausted'
                    c.sendall(struct.pack('<B3sIQ', 3, b'\0\0\0', 0, len(m)) + m)
                    return
                sig = bytes(((i * 13 + j * 31 + 7) & 255) for j in range(SIG_BYTES))
                body = struct.pack('<I', IDX0 + i) + sig
                with self.lock:
                    self.sent.append((IDX0 + i, sig))
                msg = struct.pack('<B3sIQ', 0, b'\0\0\0', 0, len(body)) + body
                for o in range(0, len(msg), 700):
                    c.sendall(msg[o:o + 700])
                    time.sleep(0.0002)
        except (EOFError, OSError):
            pass
        finally:
            c.close()


class Env:
    def __init__(self):
        self.tmp = tempfile.mkdtemp()
        self.sdir = tempfile.mkdtemp(prefix='rf', dir='/tmp')    # a unix socket path is short
        self.cnt = 0

    def fake(self, mode='ok'):
        self.cnt += 1
        path = os.path.join(self.sdir, 's%d' % self.cnt)
        return path, Fake(path, mode)

    def dir(self, files):
        self.cnt += 1
        d = os.path.join(self.tmp, 'd%d' % self.cnt)
        os.mkdir(d)
        for k, v in files.items():
            open(os.path.join(d, k), 'wb').write(v)
        return d

    def close(self):
        shutil.rmtree(self.tmp)
        shutil.rmtree(self.sdir)


def run(prover, mode, d, sock, extra=None, expect_ok=True):
    """One request with the ready/go handshake: (proof bytes or None, stderr, exit code, done seen)."""
    env = {'RF_ORACLE': sock, 'PATH': '/usr/bin', 'RF_KECCAK_LOG': '1'}
    env.update(extra or {})
    p = subprocess.Popen(prover.split() + [mode, d], stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         env=env)
    ready = p.stdout.readline() == b'ready\n'
    done = False
    if ready:
        p.stdin.write(b'go\n')
        p.stdin.flush()
        done = p.stdout.readline() == b'done\n'
    out_err = p.communicate()
    err = out_err[1].decode(errors='replace')
    if expect_ok:
        assert ready and done and p.returncode == 0, (mode, d, err)
        assert 'proof.bin.tmp' not in os.listdir(d), 'proof.bin.tmp left behind'
        return open(os.path.join(d, 'proof.bin'), 'rb').read(), err, 0, True
    return None, err, p.returncode, ready and done


def kernel_line(err):
    for line in err.splitlines():
        if line.startswith('prover: keccak '):
            return line[len('prover: keccak '):]
    return None


def main():
    ref, fast, kernels = sys.argv[1], sys.argv[2], sys.argv[3].split()
    E = Env()
    ok = True
    rnd = lambda: os.urandom(32).hex()
    chain = lambda n: json.dumps({'n': n, 'start': rnd()}).encode()

    def check(tag, good, detail=''):
        nonlocal ok
        print('%-62s %s%s' % (tag, 'ok' if good else 'FAILED', (' ' + detail) if detail else ''))
        ok &= bool(good)

    # prover setup: writes DIR/keccak naming one of the kernels this CPU runs
    setup = E.dir({})
    sp = subprocess.run(fast.split() + ['setup', setup], capture_output=True, text=True)
    chosen = open(os.path.join(setup, 'keccak')).read().strip() if os.path.exists(os.path.join(setup, 'keccak')) else None
    check('setup: exit 0, DIR/keccak names a kernel this CPU runs (%s)' % chosen,
          sp.returncode == 0 and chosen in kernels, sp.stdout.strip().replace('\n', '; '))
    bad_setup = E.dir({'keccak': b'nonexistent\n'})
    empty_setup = E.dir({})

    # how each case chooses its kernel, and what RF_KECCAK_LOG must then say
    cases = [('RF_KECCAK=%s' % k, {'RF_KECCAK': k}, '%s (forced)' % k) for k in kernels]
    cases += [('setup', {'RF_SETUP': setup}, '%s (setup)' % chosen),
              ('setup file missing', {'RF_SETUP': empty_setup}, ' (timed)'),
              ('setup file names no kernel', {'RF_SETUP': bad_setup}, ' (timed)'),
              ('no RF_SETUP', {}, ' (timed)')]
    streams = [[(1, 2), 5, 100000, 3, 0], [(3000, 7000), 1000], [(131073, 131072), 7], [(0, 4), 2]]
    if os.environ.get('TP_QUICK'):
        streams = [[(1, 2), 5, 3, 0], [(300, 700), 100], [(0, 4), 2]]
    for name, extra, want in cases:
        for si, plan in enumerate(streams):
            files = {}
            for who, prover, env in (('ref', ref, {}), ('fast', fast, extra)):
                sock, fake = E.fake()
                outs, logs = [], []
                prev = None
                for j, item in enumerate(plan):
                    if j == 0:
                        if who == 'ref':
                            files[j] = {'chainA.json': chain(item[0]), 'chainB.json': chain(item[1])}
                        proof, err, _, _ = run(prover, 'first', E.dir(files[j]), sock, env)
                    else:
                        if who == 'ref':
                            files[j] = {'chain.json': chain(item), 'prev.stmt': (rnd() + ('\n' if j % 2 else '')).encode()}
                        proof, err, _, _ = run(prover, 'step', E.dir(dict(files[j], **{'prev.bin': prev})), sock, env)
                    last = fake.sent[-1]
                    if proof[-(8 + SIG_BYTES):] != struct.pack('<Q', last[0]) + last[1]:
                        check('%s %s: request %d carries the last SIGN reply' % (who, name, j), False)
                    outs.append(proof)
                    logs.append(err)
                    prev = proof
                files[who] = (outs, fake.signs, len(fake.bad), logs)
            r, f = files['ref'], files['fast']
            same = r[0] == f[0]
            check('%-26s stream %d (%d requests): files equal' % (name, si, len(plan)), same,
                  '' if same else 'first difference in request %d' % next(i for i in range(len(r[0])) if r[0][i] != f[0][i]))
            check('%-26s stream %d: %d SIGNs each, no bad header' % (name, si, r[1]), r[1] == f[1] and r[2] == f[2] == 0)
            said = [kernel_line(e) for e in f[3]]
            good = all(s is not None and (s == want if not want.startswith(' ') else s.endswith(want)) for s in said)
            check('%-26s stream %d: the prover says "%s"' % (name, si, said[0]), good)

    # a stream long enough that prev.bin grows past 250 KB, with the setup's kernel
    plan = [(150, 160)] + [200 + i for i in range(10 if os.environ.get('TP_QUICK') else 30)]
    res = {}
    for who, prover, env in (('ref', ref, {}), ('fast', fast, {'RF_SETUP': setup})):
        sock, fake = E.fake()
        rng_files, prev, outs = [], None, []
        for j, item in enumerate(plan):
            if who == 'ref':
                rng_files.append({'chainA.json': chain(item[0]), 'chainB.json': chain(item[1])} if j == 0 else
                                 {'chain.json': chain(item), 'prev.stmt': (rnd() + '\n').encode()})
            fl = res['ref_files'][j] if who == 'fast' else rng_files[j]
            if j == 0:
                proof, _, _, _ = run(prover, 'first', E.dir(fl), sock, env)
            else:
                proof, _, _, _ = run(prover, 'step', E.dir(dict(fl, **{'prev.bin': prev})), sock, env)
            prev = proof
            outs.append(proof)
        if who == 'ref':
            res['ref_files'] = rng_files
        res[who] = outs
    check('setup, a %d-request stream: files equal (last %d bytes)' % (len(plan), len(res['ref'][-1])), res['ref'] == res['fast'])

    # failures
    _, err, code, done = run(fast, 'first', E.dir({'chainA.json': chain(5), 'chainB.json': chain(5)}), E.fake()[0],
                             {'RF_KECCAK': 'nonexistent'}, expect_ok=False)
    check('RF_KECCAK naming no usable kernel: exit 1 before ready', code == 1 and not done and 'RF_KECCAK' in err)
    for k in ('scalar', 'bmi', 'avx512', 'avx512vl', 'avx512vln'):
        if k not in kernels:
            _, err, code, done = run(fast, 'first', E.dir({'chainA.json': chain(5), 'chainB.json': chain(5)}),
                                     E.fake()[0], {'RF_KECCAK': k}, expect_ok=False)
            check('RF_KECCAK=%s, which this CPU cannot run: exit 1 before ready' % k,
                  code == 1 and not done and 'RF_KECCAK' in err)
    sock, _ = E.fake('refuse')
    d = E.dir({'chainA.json': chain(2000), 'chainB.json': chain(2000)})
    _, err, code, done = run(fast, 'first', d, sock, {'RF_SETUP': setup}, expect_ok=False)
    check('a refused SIGN: exit 1, no done, no proof.bin', code == 1 and not done and 'proof.bin' not in os.listdir(d),
          err.strip().splitlines()[-1] if err.strip() else '')
    sock, _ = E.fake()
    prev, _, _, _ = run(ref, 'first', E.dir({'chainA.json': chain(5), 'chainB.json': chain(5)}), sock)
    d = E.dir({'prev.bin': prev[:-1], 'prev.stmt': rnd().encode(), 'chain.json': chain(2000)})
    _, err, code, done = run(fast, 'step', d, E.fake()[0], {'RF_SETUP': setup}, expect_ok=False)
    check('a truncated prev.bin: exit 1, no done, no proof.bin',
          code == 1 and not done and 'proof.bin' not in os.listdir(d) and 'malformed' in err)
    E.close()
    print('all passed' if ok else 'FAILED')
    sys.exit(0 if ok else 1)


main()
