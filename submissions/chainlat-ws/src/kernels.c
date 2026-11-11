/* chainwalk kernels: reference, scalar-BMI2 and AVX-512VL chain walkers + self-test.
 * k_vec layout: R_y (y=0..4) slots 0..3 = lanes x+5y (x=0..3); S slots 0..3 = lanes
 * 4+5y (y=0..3); GP t = lane 24.  pi: out lane (x,y) <- in lane ((x+3y)%5) + 5x.
 * vpermi2q ymm idx: 0..3 = first source, 4..7 = second source.
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <immintrin.h>
#include <cpuid.h>

static const uint64_t RC[24] = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808aull, 0x8000000080008000ull,
    0x000000000000808bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000aull,
    0x000000008000808bull, 0x800000000000008bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800aull, 0x800000008000000aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull,};
static const int RHO[25] = {0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                            41, 45, 15, 21, 8, 18, 2, 61, 56, 14};
#define ROL(v, n) (((v) << (n)) | ((v) >> ((64 - (n)) & 63)))

static void keccak_f(uint64_t a[25]) {
    for (int r = 0; r < 24; r++) {
        uint64_t c[5], b[25];
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++)
            for (int y = 0; y < 25; y += 5) a[x + y] ^= c[(x + 4) % 5] ^ ROL(c[(x + 1) % 5], 1);
        for (int x = 0; x < 5; x++)
            for (int y = 0; y < 5; y++) b[y + 5 * ((2 * x + 3 * y) % 5)] = ROL(a[x + 5 * y], RHO[x + 5 * y]);
        for (int y = 0; y < 25; y += 5)
            for (int x = 0; x < 5; x++) a[x + y] = b[x + y] ^ (~b[(x + 1) % 5 + y] & b[(x + 2) % 5 + y]);
        a[0] ^= RC[r];
    }
}

static void chain_words_c(uint64_t w[4], uint64_t n) {
    uint64_t a[25];
    while (n--) {
        memset(a, 0, sizeof a);
        a[0] = 0x43 ^ (w[0] << 8);
        a[1] = (w[0] >> 56) ^ (w[1] << 8);
        a[2] = (w[1] >> 56) ^ (w[2] << 8);
        a[3] = (w[2] >> 56) ^ (w[3] << 8);
        a[4] = (w[3] >> 56) ^ 0x0100ull;
        a[16] = 0x8000000000000000ull;
        keccak_f(a);
        w[0] = a[0]; w[1] = a[1]; w[2] = a[2]; w[3] = a[3];
    }
}

/* --------------------------------------------------------------- scalar BMI2 */
#define RB(r)                                                                     \
    {                                                                             \
        uint64_t c0, c1, c2, c3, c4, d0, d1, d2, d3, d4;                          \
        c0 = a0 ^ a5 ^ a10 ^ a15 ^ a20;                                           \
        c1 = a1 ^ a6 ^ a11 ^ a16 ^ a21;                                           \
        c2 = a2 ^ a7 ^ a12 ^ a17 ^ a22;                                           \
        c3 = a3 ^ a8 ^ a13 ^ a18 ^ a23;                                           \
        c4 = a4 ^ a9 ^ a14 ^ a19 ^ a24;                                           \
        d0 = c4 ^ ROL(c1, 1); d1 = c0 ^ ROL(c2, 1); d2 = c1 ^ ROL(c3, 1);         \
        d3 = c2 ^ ROL(c4, 1); d4 = c3 ^ ROL(c0, 1);                               \
        a0 ^= d0; a1 ^= d1; a2 ^= d2; a3 ^= d3; a4 ^= d4;                         \
        a5 ^= d0; a6 ^= d1; a7 ^= d2; a8 ^= d3; a9 ^= d4;                         \
        a10 ^= d0; a11 ^= d1; a12 ^= d2; a13 ^= d3; a14 ^= d4;                    \
        a15 ^= d0; a16 ^= d1; a17 ^= d2; a18 ^= d3; a19 ^= d4;                    \
        a20 ^= d0; a21 ^= d1; a22 ^= d2; a23 ^= d3; a24 ^= d4;                    \
        b0 = ROL(a0, 0); b1 = ROL(a6, 44); b2 = ROL(a12, 43); b3 = ROL(a18, 21);  \
        b4 = ROL(a24, 14);                                                        \
        b5 = ROL(a3, 28); b6 = ROL(a9, 20); b7 = ROL(a10, 3); b8 = ROL(a16, 45);  \
        b9 = ROL(a22, 61);                                                        \
        b10 = ROL(a1, 1); b11 = ROL(a7, 6); b12 = ROL(a13, 25);                   \
        b13 = ROL(a19, 8); b14 = ROL(a20, 18);                                    \
        b15 = ROL(a4, 27); b16 = ROL(a5, 36); b17 = ROL(a11, 10);                 \
        b18 = ROL(a17, 15); b19 = ROL(a23, 56);                                   \
        b20 = ROL(a2, 62); b21 = ROL(a8, 55); b22 = ROL(a14, 39);                 \
        b23 = ROL(a15, 41); b24 = ROL(a21, 2);                                    \
        a0 = b0 ^ (~b1 & b2); a1 = b1 ^ (~b2 & b3); a2 = b2 ^ (~b3 & b4);         \
        a3 = b3 ^ (~b4 & b0); a4 = b4 ^ (~b0 & b1);                               \
        a5 = b5 ^ (~b6 & b7); a6 = b6 ^ (~b7 & b8); a7 = b7 ^ (~b8 & b9);         \
        a8 = b8 ^ (~b9 & b5); a9 = b9 ^ (~b5 & b6);                               \
        a10 = b10 ^ (~b11 & b12); a11 = b11 ^ (~b12 & b13); a12 = b12 ^ (~b13 & b14); \
        a13 = b13 ^ (~b14 & b10); a14 = b14 ^ (~b10 & b11);                       \
        a15 = b15 ^ (~b16 & b17); a16 = b16 ^ (~b17 & b18); a17 = b17 ^ (~b18 & b19); \
        a18 = b18 ^ (~b19 & b15); a19 = b19 ^ (~b15 & b16);                       \
        a20 = b20 ^ (~b21 & b22); a21 = b21 ^ (~b22 & b23); a22 = b22 ^ (~b23 & b24); \
        a23 = b23 ^ (~b24 & b20); a24 = b24 ^ (~b20 & b21);                       \
        a0 ^= RC[r];                                                              \
    }

__attribute__((target("bmi2")))
static void chain_words_gp(uint64_t w[4], uint64_t n) {
    uint64_t a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21, a22, a23, a24, b0, b1, b2, b3, b4, b5, b6, b7,
        b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24;
    while (n--) {
        a0 = 0x43 ^ (w[0] << 8);
        a1 = (w[0] >> 56) ^ (w[1] << 8);
        a2 = (w[1] >> 56) ^ (w[2] << 8);
        a3 = (w[2] >> 56) ^ (w[3] << 8);
        a4 = (w[3] >> 56) ^ 0x0100ull;
        a16 = 0x8000000000000000ull;
        a5 = a6 = a7 = a8 = a9 = a10 = a11 = a12 = a13 = a14 = a15 = 0;
        a17 = a18 = a19 = a20 = a21 = a22 = a23 = a24 = 0;
        RB(0) RB(1) RB(2) RB(3) RB(4) RB(5) RB(6) RB(7) RB(8) RB(9) RB(10) RB(11)
        RB(12) RB(13) RB(14) RB(15) RB(16) RB(17) RB(18) RB(19) RB(20) RB(21) RB(22) RB(23)
        w[0] = a0; w[1] = a1; w[2] = a2; w[3] = a3;
    }
}

/* --------------------------------------------------------------- AVX-512VL */
#define A64 static const uint64_t __attribute__((aligned(32)))
A64 K1[4] = {1, 1, 1, 1};
A64 KRHO0[4] = {0, 1, 62, 28};
A64 KRHO1[4] = {36, 44, 6, 55};
A64 KRHO2[4] = {3, 10, 43, 25};
A64 KRHO3[4] = {41, 45, 15, 21};
A64 KRHO4[4] = {18, 2, 61, 56};
A64 KRHOS[4] = {27, 20, 39, 8};
A64 RCv[24][4] = {
    {0x0000000000000001ull, 0, 0, 0}, {0x0000000000008082ull, 0, 0, 0},
    {0x800000000000808Aull, 0, 0, 0}, {0x8000000080008000ull, 0, 0, 0},
    {0x000000000000808Bull, 0, 0, 0}, {0x0000000080000001ull, 0, 0, 0},
    {0x8000000080008081ull, 0, 0, 0}, {0x8000000000008009ull, 0, 0, 0},
    {0x000000000000008Aull, 0, 0, 0}, {0x0000000000000088ull, 0, 0, 0},
    {0x8000000080008009ull, 0, 0, 0}, {0x800000008000000Aull, 0, 0, 0},
    {0x800000008000808Bull, 0, 0, 0}, {0x800000008000808Bull, 0, 0, 0},
    {0x8000000000008089ull, 0, 0, 0}, {0x8000000000008003ull, 0, 0, 0},
    {0x8000000000008002ull, 0, 0, 0}, {0x8000000000000080ull, 0, 0, 0},
    {0x000000000000800Aull, 0, 0, 0}, {0x800000008000000Aull, 0, 0, 0},
    {0x8000000080008081ull, 0, 0, 0}, {0x8000000080008080ull, 0, 0, 0},
    {0x0000000080000001ull, 0, 0, 0}, {0x8000000080008008ull, 0, 0, 0}};
A64 TH_L[4] = {0, 0, 1, 2};   /* L = [C4, C0, C1, C2] */
A64 TH_R[4] = {1, 2, 3, 0};   /* R = [rC1, rC2, rC3, _] */
A64 PI0_A[4] = {0, 5, 0, 0};  /* R0,R1 -> [R0[0], R1[1]] */
A64 PI0_B[4] = {2, 7, 0, 0};  /* R2,R3 -> [R2[2], R3[3]] */
A64 PI0_C[4] = {0, 1, 4, 5};
A64 PI1_A[4] = {3, 5, 0, 0};  /* R0,S  -> [R0[3], S[1]] */
A64 PI1_B[4] = {0, 5, 0, 0};  /* R2,R3 -> [R2[0], R3[1]] */
A64 PI1_C[4] = {0, 1, 4, 5};
A64 PI2_A[4] = {1, 6, 0, 0};  /* R0,R1 -> [R0[1], R1[2]] */
A64 PI2_B[4] = {3, 7, 0, 0};  /* R2,S  -> [R2[3], S[3]] */
A64 PI2_C[4] = {0, 1, 4, 5};
A64 PI3_A[4] = {0, 5, 0, 0};  /* R1,R2 -> [R1[0], R2[1]] */
A64 PI3_B[4] = {2, 4, 0, 0};  /* R3,S  -> [R3[2], S[0]] */
A64 PI3_C[4] = {5, 0, 1, 4};  /* -> [S[0], R1[0], R2[1], R3[2]] */
A64 PIS_P[4] = {0, 2, 0, 3};  /* R4 -> [_, R4[2], R4[0], R4[3]] */
A64 PI4_A[4] = {2, 7, 0, 0};  /* R0,R1 -> [R0[2], R1[3]] */
A64 PI4_B[4] = {2, 4, 0, 0};  /* S,R3  -> [S[2], R3[0]]  */
A64 PI4_C[4] = {0, 1, 4, 5};
A64 CH_L0[4] = {1, 2, 3, 4};
A64 CH_L1[4] = {1, 2, 3, 5};
A64 CH_L2[4] = {1, 2, 3, 6};
A64 CH_L3[4] = {1, 2, 3, 7};
A64 CH_L4[4] = {1, 2, 3, 4};
A64 CH_R0[4] = {2, 3, 4, 0};
A64 CH_R1[4] = {2, 3, 5, 0};
A64 CH_R2[4] = {2, 3, 6, 0};
A64 CH_R3[4] = {2, 3, 7, 0};
A64 CH_R4[4] = {2, 3, 4, 0};
A64 CH_C0[4] = {0, 1, 4, 5};   /* [R0[k], R1[k], R2[k], R3[k]] from lo/hi unpacks */
A64 SWAP[4] = {2, 3, 0, 1};

#define V(x) _mm256_loadu_si256((const __m256i *)(const void *)(x))
#define P2(a, i, b) _mm256_permutex2var_epi64((a), V(i), (b))
#define P2R(a, i, b) _mm256_permutex2var_epi64((a), (i), (b))
#define PV(m, i) _mm256_permutexvar_epi64(V(i), (m))
#define GX(m, i) _mm256_extract_epi64((m), (i))
#define TL(a, b, c) _mm256_ternarylogic_epi64((a), (b), (c), 0xD2) /* a ^ (~b & c) */

#include "xmm_kernel.h"

/* --------------------------------------------------------------- test */
static uint64_t xs = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { xs ^= xs << 13; xs ^= xs >> 7; xs ^= xs << 17; return xs; }

int main(int argc, char **argv) {
    int iters = argc > 1 ? atoi(argv[1]) : 40;
    for (int it = 0; it < iters; it++) {
        uint64_t wc[4] = {rnd(), rnd(), rnd(), rnd()}, wg[4], wv[4];
        uint64_t n = 1 + (rnd() % 5) + (it % 3) * 40;
        memcpy(wg, wc, 32); memcpy(wv, wc, 32);
        chain_words_c(wc, n); chain_words_gp(wg, n); chain_words_vec(wv, n);
        if (memcmp(wc, wg, 32) || memcmp(wc, wv, 32)) {
            printf("FAIL it=%d n=%lu c=%016lx gp=%016lx vec=%016lx\n", it, (unsigned long)n,
                   (unsigned long)wc[0], (unsigned long)wg[0], (unsigned long)wv[0]);
            return 1;
        }
    }
    printf("kernels agree on %d chains\n", iters);
    return 0;
}
