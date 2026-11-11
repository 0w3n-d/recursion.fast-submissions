/* Keccak-f[1600] chain steps with AVX-512F: one state, row y of the 5x5 lane array in the low five
   qwords of the vector R[y].  Every function carries target("avx512f") so that the file compiles at
   the baseline x86-64 target; the callers dispatch on cpuid. */
#include <immintrin.h>
#define V512 __m512i
#define E512(...) _mm512_set_epi64(__VA_ARGS__)

/* The iota constants as vectors: the round constant in the qword that holds lane 0 of row 0. */
#define RC_LIST(X)                                                                                             \
    X(0x0000000000000001ull) X(0x0000000000008082ull) X(0x800000000000808Aull) X(0x8000000080008000ull)        \
    X(0x000000000000808Bull) X(0x0000000080000001ull) X(0x8000000080008081ull) X(0x8000000000008009ull)        \
    X(0x000000000000008Aull) X(0x0000000000000088ull) X(0x0000000080008009ull) X(0x000000008000000Aull)        \
    X(0x000000008000808Bull) X(0x800000000000008Bull) X(0x8000000000008089ull) X(0x8000000000008003ull)        \
    X(0x8000000000008002ull) X(0x8000000000000080ull) X(0x000000000000800Aull) X(0x800000008000000Aull)        \
    X(0x8000000080008081ull) X(0x8000000000008080ull) X(0x0000000080000001ull) X(0x8000000080008008ull)
#define RC_ROW0(x) {x, 0, 0, 0, 0, 0, 0, 0},
static const uint64_t RC_V0[24][8] __attribute__((aligned(64))) = {RC_LIST(RC_ROW0)};

#define TL(a, b, c, imm) _mm512_ternarylogic_epi64(a, b, c, imm)
#define PM(i, a) _mm512_permutexvar_epi64(i, a)
#define BL(k, a, b) _mm512_mask_blend_epi64(k, a, b)
#define PI_IDX(y, x) (((x) + 3 * (y)) % 5)

/* Constants.  Row y holds lane x of the 5x5 array in qword x (qwords 5..7 are don't-care).  The index
   vectors are written high qword first. */
#define CONSTS512                                                                                              \
    const V512 ip = E512(7, 6, 5, 3, 2, 1, 0, 4), inx = E512(7, 6, 5, 0, 4, 3, 2, 1);                          \
    const V512 rot1 = inx, rot2 = E512(7, 6, 5, 1, 0, 4, 3, 2);                                                \
    const V512 rho0 = E512(0, 0, 0, 27, 28, 62, 1, 0), rho1 = E512(0, 0, 0, 20, 55, 6, 44, 36);               \
    const V512 rho2 = E512(0, 0, 0, 39, 25, 43, 10, 3), rho3 = E512(0, 0, 0, 8, 21, 15, 45, 41);              \
    const V512 rho4 = E512(0, 0, 0, 14, 56, 61, 2, 18)

/* pi from the rho-rotated rows a0..a4: new row Y has, at position x, old row x's lane (x + 3Y) % 5. Row 0
   is the diagonal (blends); the others gather with two two-source permutes, one permute and one OR. */
#define PIROW0(out)                                                                                            \
    out = BL(0x10, BL(0x0C, BL(0x02, a0, a1), BL(0x08, a2, a3)), a4)
#define PIROW(Y, out)                                                                                          \
    do {                                                                                                       \
        V512 u_ = _mm512_maskz_permutex2var_epi64(0x03, a0, E512(0, 0, 0, 0, 0, 0, 8 + PI_IDX(Y, 1), PI_IDX(Y, 0)), a1); \
        V512 v_ = _mm512_maskz_permutex2var_epi64(0x0C, a2, E512(0, 0, 0, 0, 8 + PI_IDX(Y, 3), PI_IDX(Y, 2), 0, 0), a3); \
        V512 w_ = _mm512_maskz_permutexvar_epi64(0x10, E512(0, 0, 0, PI_IDX(Y, 4), 0, 0, 0, 0), a4);            \
        out = TL(u_, v_, w_, 0xFE);                                                                            \
    } while (0)
#define PI_ALL(n0, n1, n2, n3, n4) do { PIROW0(n0); PIROW(1, n1); PIROW(2, n2); PIROW(3, n3); PIROW(4, n4); } while (0)

/* theta from the five rows (one permute level), chi with two rotations per row. */
#define THETA_A                                                                                                \
    V512 c = TL(r0, r1, r2, 0x96);                                                                             \
    c = TL(c, r3, r4, 0x96);                                                                                   \
    V512 p1 = PM(ip, c);                                                                                       \
    V512 p2 = _mm512_rol_epi64(PM(inx, c), 1);                                                                 \
    V512 a0 = _mm512_rolv_epi64(TL(r0, p1, p2, 0x96), rho0);                                                   \
    V512 a1 = _mm512_rolv_epi64(TL(r1, p1, p2, 0x96), rho1);                                                   \
    V512 a2 = _mm512_rolv_epi64(TL(r2, p1, p2, 0x96), rho2);                                                   \
    V512 a3 = _mm512_rolv_epi64(TL(r3, p1, p2, 0x96), rho3);                                                   \
    V512 a4 = _mm512_rolv_epi64(TL(r4, p1, p2, 0x96), rho4)
#define ROUND512(rcv)                                                                                          \
    do {                                                                                                       \
        THETA_A;                                                                                               \
        V512 n0, n1, n2, n3, n4;                                                                               \
        PI_ALL(n0, n1, n2, n3, n4);                                                                            \
        r0 = TL(n0, PM(rot1, n0), PM(rot2, n0), 0xD2);                                                         \
        r1 = TL(n1, PM(rot1, n1), PM(rot2, n1), 0xD2);                                                         \
        r2 = TL(n2, PM(rot1, n2), PM(rot2, n2), 0xD2);                                                         \
        r3 = TL(n3, PM(rot1, n3), PM(rot2, n3), 0xD2);                                                         \
        r4 = TL(n4, PM(rot1, n4), PM(rot2, n4), 0xD2);                                                         \
        r0 = _mm512_xor_si512(r0, _mm512_load_si512(rcv));                                                     \
    } while (0)
/* The last round keeps only row 0, lanes 0..3 (the digest): pi row 0 is a diagonal of the rho'd rows. */
#define LAST_ROUND512(rcv)                                                                                     \
    do {                                                                                                       \
        THETA_A;                                                                                               \
        V512 n0;                                                                                               \
        PIROW0(n0);                                                                                            \
        r0 = TL(n0, PM(rot1, n0), PM(rot2, n0), 0xD2);                                                         \
        r0 = _mm512_xor_si512(r0, _mm512_load_si512(rcv));                                                     \
    } while (0)
#define ROUNDS_A                                                                                               \
    ROUND512(RC_V0[0]); ROUND512(RC_V0[1]); ROUND512(RC_V0[2]); ROUND512(RC_V0[3]);                            \
    ROUND512(RC_V0[4]); ROUND512(RC_V0[5]); ROUND512(RC_V0[6]); ROUND512(RC_V0[7]);                            \
    ROUND512(RC_V0[8]); ROUND512(RC_V0[9]); ROUND512(RC_V0[10]); ROUND512(RC_V0[11]);                          \
    ROUND512(RC_V0[12]); ROUND512(RC_V0[13]); ROUND512(RC_V0[14]); ROUND512(RC_V0[15]);                        \
    ROUND512(RC_V0[16]); ROUND512(RC_V0[17]); ROUND512(RC_V0[18]); ROUND512(RC_V0[19]);                        \
    ROUND512(RC_V0[20]); ROUND512(RC_V0[21]); ROUND512(RC_V0[22]); LAST_ROUND512(RC_V0[23])

#define LOAD_ROWS512                                                                                           \
    V512 r0 = _mm512_maskz_loadu_epi64(0x1F, st), r1 = _mm512_maskz_loadu_epi64(0x1F, st + 5);                 \
    V512 r2 = _mm512_maskz_loadu_epi64(0x1F, st + 10), r3 = _mm512_maskz_loadu_epi64(0x1F, st + 15);           \
    V512 r4 = _mm512_maskz_loadu_epi64(0x1F, st + 20)
#define STORE_ROW0_512 _mm512_mask_storeu_epi64(st, 0x1F, r0)
/* Only the digest (lanes 0..3 of row 0) is meaningful after the last round. */
#define PERMUTE_FN(name, ROUNDS)                                                                               \
    __attribute__((target("avx512f"))) static void name(uint64_t st[25]) {                                     \
        CONSTS512;                                                                                             \
        LOAD_ROWS512;                                                                                          \
        ROUNDS;                                                                                                \
        _mm512_mask_storeu_epi64(st, 0x0F, r0);                                                                \
    }
/* the digest only: lanes 0..3 of st afterwards (the rest is not computed) */
PERMUTE_FN(keccak_f_digest_avx512, ROUNDS_A)

/* n steps of d <- Keccak-256(0x43 || d), the 33-byte message padded in place */
#define CHAIN_FN(name, ROUNDS)                                                                                 \
    __attribute__((target("avx512f"))) static void name(uint8_t out[32], const uint8_t in[32], uint64_t n) {   \
        CONSTS512;                                                                                             \
        uint64_t h[4];                                                                                         \
        memcpy(h, in, 32);                                                                                     \
        V512 d = _mm512_maskz_loadu_epi64(0x0F, h);                                                            \
        const V512 pad0 = E512(0, 0, 0, 0x100, 0, 0, 0, 0x43);                                                 \
        const V512 pad3 = E512(0, 0, 0, 0, 0, 0, (long long)0x8000000000000000ull, 0);                         \
        const V512 lift = E512(7, 6, 5, 3, 2, 1, 0, 7);  /* lane i <- lane i-1; lane 0 is masked off */        \
        for (uint64_t it = 0; it < n; it++) {                                                                  \
            V512 lo = _mm512_maskz_slli_epi64(0x0F, d, 8);                                                     \
            V512 hi = _mm512_maskz_permutexvar_epi64(0x1E, lift, _mm512_srli_epi64(d, 56));                    \
            V512 r0 = TL(lo, hi, pad0, 0xFE);                                                                  \
            V512 r1 = _mm512_setzero_si512(), r2 = r1, r3 = pad3, r4 = r1;                                     \
            ROUNDS;                                                                                            \
            d = r0;                                                                                            \
        }                                                                                                      \
        _mm512_mask_storeu_epi64(h, 0x0F, d);                                                                  \
        memcpy(out, h, 32);                                                                                    \
    }
CHAIN_FN(chain_avx512, ROUNDS_A)
