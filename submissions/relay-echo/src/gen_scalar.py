#!/usr/bin/env python3
"""Generates keccak_scalar.inc: Keccak-f[1600] chain steps, fully unrolled, lane complementing.

The complement pattern F (a lane is stored as ~lane when F[lane]) is a fixed point of the round, so
that no explicit NOT is needed except where the 5-cycle of a chi row forces one.  The pattern is found
by a search that this script reruns (deterministically) every time.
Usage: gen_scalar.py > keccak_scalar.inc
"""
import random, sys, itertools

RC = [0x0000000000000001,0x0000000000008082,0x800000000000808A,0x8000000080008000,
      0x000000000000808B,0x0000000080000001,0x8000000080008081,0x8000000000008009,
      0x000000000000008A,0x0000000000000088,0x0000000080008009,0x000000008000000A,
      0x000000008000808B,0x800000000000008B,0x8000000000008089,0x8000000000008003,
      0x8000000000008002,0x8000000000000080,0x000000000000800A,0x800000008000000A,
      0x8000000080008081,0x8000000000008080,0x0000000080000001,0x8000000080008008]
RHO = [0,1,62,28,27,36,44,6,55,20,3,10,43,25,39,41,45,15,21,8,18,2,61,56,14]

def row_plan(g, target):
    """g: flags of b0..b4 of a chi row; target: wanted out flags.
    Returns (cost, notmask, uses) or None.  notmask: lanes whose NOT is computed (one instruction each; both
    polarities are then usable); uses[i] = (flip1, flip2, flipbase, outnot) for output lane i."""
    best = None
    for mask in range(32):
        cost = bin(mask).count('1'); uses = []; ok = True
        for i in range(5):
            j1, j2 = (i+1) % 5, (i+2) % 5
            opts = []
            for fl1 in ((0, 1) if (mask >> j1) & 1 else (0,)):
                for fl2 in ((0, 1) if (mask >> j2) & 1 else (0,)):
                    for flb in ((0, 1) if (mask >> i) & 1 else (0,)):
                        f1 = g[j1] ^ fl1; f2 = g[j2] ^ fl2
                        if (f1, f2) == (1, 0): op, d = 'and', 0
                        elif (f1, f2) == (0, 1): op, d = 'or', 1
                        else: continue
                        of = g[i] ^ flb ^ d
                        opts.append((int(of != target[i]), op, fl1, fl2, flb))
            if not opts: ok = False; break
            o = min(opts); cost += o[0]; uses.append(o)
        if ok and (best is None or cost < best[0]): best = (cost, mask, uses)
    return best

def round_flags(F):
    """Flags after theta, rho, pi (b-array, index x'+5y'), or None."""
    cf = [F[x]^F[x+5]^F[x+10]^F[x+15]^F[x+20] for x in range(5)]
    df = [cf[(x+4)%5]^cf[(x+1)%5] for x in range(5)]
    b = [0]*25
    for x in range(5):
        for y in range(5):
            b[y + 5*((2*x+3*y)%5)] = F[x+5*y] ^ df[x]
    return b

def cost(F):
    b = round_flags(F); tot = 0; plans = []
    for y in range(5):
        p = row_plan(b[5*y:5*y+5], F[5*y:5*y+5])
        if p is None: return None, None
        tot += p[0]; plans.append(p)
    return tot, plans

def search():
    rng = random.Random(1)
    xkcp = [0]*25
    for l in (1, 2, 8, 12, 17, 20): xkcp[l] = 1
    c, p = cost(xkcp)
    if c is not None: return xkcp, c, p
    best = None
    for _ in range(200000):
        F = [rng.randint(0, 1) for _ in range(25)]
        c, p = cost(F)
        if c is not None and (best is None or c < best[1]): best = (F, c, p)
    return best

def emit_rounds(w, F, plans_cur, last_only=None):
    """Emits the 24 rounds on lanes named a0..a24 (stored polarity F); returns the names of the output lanes."""
    cur = ['a%d' % i for i in range(25)]
    for r in range(24):
        p = "r%d_" % r
        for x in range(5):
            w("        uint64_t %sc%d = ((%s ^ %s) ^ (%s ^ %s)) ^ %s;" % (p, x, cur[x], cur[x+5], cur[x+10], cur[x+15], cur[x+20]))
        for x in range(5):
            w("        uint64_t %sd%d = %sc%d ^ ROL64(%sc%d, 1);" % (p, x, p, (x+4)%5, p, (x+1)%5))
        b = [None]*25
        for x in range(5):
            for y in range(5):
                i = x+5*y; j = y + 5*((2*x+3*y)%5)
                nm = "%sb%d" % (p, j)
                if RHO[i]:
                    w("        uint64_t %s = ROL64(%s ^ %sd%d, %d);" % (nm, cur[i], p, x, RHO[i]))
                else:
                    w("        uint64_t %s = %s ^ %sd%d;" % (nm, cur[i], p, x))
                b[j] = nm
        bf = round_flags(F)
        nxt = [None]*25
        for y in range(5):
            cst, mask, uses = row_plan(bf[5*y:5*y+5], F[5*y:5*y+5])
            nb = {}
            for j in range(5):
                if (mask >> j) & 1:
                    nb[j] = "%sn%d" % (p, 5*y+j)
                    w("        uint64_t %s = ~%s;" % (nb[j], b[5*y+j]))
            def pick(j, fl):
                return nb[j] if fl else b[5*y+j]
            for i in range(5):
                j1, j2 = (i+1)%5, (i+2)%5
                onot, op, fl1, fl2, flb = uses[i]
                s1 = pick(j1, fl1); s2 = pick(j2, fl2); sb = pick(i, flb)
                op = '&' if op == 'and' else '|'
                nm = "%se%d" % (p, 5*y+i)
                rc = (" ^ 0x%016Xull" % RC[r]) if (y == 0 and i == 0) else ""
                w("        uint64_t %s = %s(%s ^ (%s %s %s))%s;" % (nm, "~" if onot else "", sb, s1, op, s2, rc))
                nxt[5*y+i] = nm
        cur = nxt
    return cur

def gen():
    F, c, plans = search()
    out = []
    w = out.append
    w("/* generated by gen_scalar.py (do not edit): Keccak-f[1600], 24 rounds unrolled, lane complementing.")
    w("   Complemented lanes: %s; explicit NOTs per round: %d. */" % ([i for i in range(25) if F[i]], c))
    w("#pragma GCC diagnostic push")
    w("#pragma GCC diagnostic ignored \"-Wunused-variable\"   /* the chain's last round computes lanes it drops */")
    w("#define ROL64(v, n) (((v) << (n)) | ((v) >> (64 - (n))))")
    # the whole permutation, for tests and generic use
    w("static void keccak_f_scalar(uint64_t st[25]) {")
    w("    {")
    for i in range(25):
        w("        uint64_t a%d = %sst[%d];" % (i, "~" if F[i] else "", i))
    cur = emit_rounds(w, F, None)
    for i in range(25):
        w("        st[%d] = %s%s;" % (i, "~" if F[i] else "", cur[i]))
    w("    }")
    w("}")
    # the chain: n steps of d <- Keccak-256(0x43 || d)
    w("static void chain_scalar(uint8_t out[32], const uint8_t in[32], uint64_t n) {")
    w("    uint64_t h0, h1, h2, h3;")
    w("    memcpy(&h0, in, 8); memcpy(&h1, in + 8, 8); memcpy(&h2, in + 16, 8); memcpy(&h3, in + 24, 8);")
    w("    for (uint64_t it = 0; it < n; it++) {")
    # lane k = bytes 8k..8k+7 of (0x43 || d || 0x01 || zeros || 0x80)
    init = ["0x43ull | h0 << 8", "h0 >> 56 | h1 << 8", "h1 >> 56 | h2 << 8", "h2 >> 56 | h3 << 8",
            "h3 >> 56 | 0x100ull"] + ["0"]*11 + ["0x8000000000000000ull"] + ["0"]*8
    for i in range(25):
        v = init[i]
        if F[i]: v = "~(%s)" % v
        w("        uint64_t a%d = %s;" % (i, v))
    cur = emit_rounds(w, F, None)
    for i in range(4):
        w("        h%d = %s%s;" % (i, "~" if F[i] else "", cur[i]))
    w("    }")
    w("    memcpy(out, &h0, 8); memcpy(out + 8, &h1, 8); memcpy(out + 16, &h2, 8); memcpy(out + 24, &h3, 8);")
    w("}")
    w("#pragma GCC diagnostic pop")
    return "\n".join(out) + "\n"

if __name__ == "__main__":
    sys.stdout.write(gen())
