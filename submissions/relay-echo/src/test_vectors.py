#!/usr/bin/env python3
"""Independent check (a from-scratch Python Keccak-256) of the values printed by `test_keccak vectors`:
chain ends, leaf statements, node statement and keccak256("") for every available implementation."""
import subprocess, sys
M = (1 << 64) - 1
RC = [0x1,0x8082,0x800000000000808a,0x8000000080008000,0x808b,0x80000001,0x8000000080008081,0x8000000000008009,
      0x8a,0x88,0x80008009,0x8000000a,0x8000808b,0x800000000000008b,0x8000000000008089,0x8000000000008003,
      0x8000000000008002,0x8000000000000080,0x800a,0x800000008000000a,0x8000000080008081,0x8000000000008080,
      0x80000001,0x8000000080008008]
R = [[0,36,3,41,18],[1,44,10,45,2],[62,6,43,15,61],[28,55,25,21,56],[27,20,39,8,14]]   # R[x][y]
rol = lambda v, n: ((v << n) | (v >> (64 - n))) & M if n else v
def f(A):                                            # A[x][y]
    for rc in RC:
        C = [A[x][0]^A[x][1]^A[x][2]^A[x][3]^A[x][4] for x in range(5)]
        D = [C[(x-1)%5] ^ rol(C[(x+1)%5], 1) for x in range(5)]
        A = [[A[x][y] ^ D[x] for y in range(5)] for x in range(5)]
        B = [[0]*5 for _ in range(5)]
        for x in range(5):
            for y in range(5):
                B[y][(2*x+3*y)%5] = rol(A[x][y], R[x][y])
        A = [[B[x][y] ^ (~B[(x+1)%5][y] & M & B[(x+2)%5][y]) for y in range(5)] for x in range(5)]
        A[0][0] ^= rc
    return A
def keccak256(m):
    st = [[0]*5 for _ in range(5)]
    m = bytearray(m)
    m.append(1)
    while len(m) % 136: m.append(0)
    m[-1] |= 0x80
    for off in range(0, len(m), 136):
        for i in range(17):
            st[i % 5][i // 5] ^= int.from_bytes(m[off+8*i:off+8*i+8], 'little')
        st = f(st)
    return b''.join(st[i % 5][i // 5].to_bytes(8, 'little') for i in range(4))
out = subprocess.run([sys.argv[1], 'vectors'], capture_output=True, text=True, check=True).stdout.splitlines()
bad = 0; n = 0
for line in out:
    t = line.split()
    if t[0] == 'chain':
        s = bytes.fromhex(t[3]); k = int(t[2]); d = s
        for _ in range(k): d = keccak256(b'\x43' + d)
        leaf = keccak256(b'\x4c' + d + k.to_bytes(8, 'little'))
        ok = d.hex() == t[4] and leaf.hex() == t[5]
    elif t[0] == 'node':
        ok = keccak256(b'\x4e' + bytes.fromhex(t[1]) + bytes.fromhex(t[2])).hex() == t[3]
    else:
        ok = t[1] == 'c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470' and keccak256(b'').hex() == t[1]
    n += 1; bad += not ok
    if not ok: print('MISMATCH', line)
print('%d vectors, %d mismatches' % (n, bad))
sys.exit(1 if bad else 0)
