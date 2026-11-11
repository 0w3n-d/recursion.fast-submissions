/* The baseline's portable, byte-oriented Keccak-256 and the contract's statements, verbatim from
   witness-baseline/src/prover.c (the reference of the tests; the prover uses it for the short statement
   hashes, and chain.h for the long chains). */
#include <stdint.h>
#include <string.h>
/* ---- Keccak-256 (Ethereum's: FIPS 202's sponge over Keccak-f[1600], rate 136, padding 0x01 … 0x80) */
static const uint64_t RC[24] = {
    0x0000000000000001ull, 0x0000000000008082ull, 0x800000000000808Aull, 0x8000000080008000ull,
    0x000000000000808Bull, 0x0000000080000001ull, 0x8000000080008081ull, 0x8000000000008009ull,
    0x000000000000008Aull, 0x0000000000000088ull, 0x0000000080008009ull, 0x000000008000000Aull,
    0x000000008000808Bull, 0x800000000000008Bull, 0x8000000000008089ull, 0x8000000000008003ull,
    0x8000000000008002ull, 0x8000000000000080ull, 0x000000000000800Aull, 0x800000008000000Aull,
    0x8000000080008081ull, 0x8000000000008080ull, 0x0000000080000001ull, 0x8000000080008008ull};
static const int RHO[25] = {0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39,
                            41, 45, 15, 21, 8, 18, 2, 61, 56, 14};
#define ROL(v, n) (((v) << (n)) | ((v) >> ((64 - (n)) & 63)))

/* Keccak-f[1600] on 25 lanes, lane x + 5y (FIPS 202 §3.2). */
static void keccak_f(uint64_t a[25]) {
    for (int r = 0; r < 24; r++) {
        uint64_t c[5], b[25];
        for (int x = 0; x < 5; x++) c[x] = a[x] ^ a[x + 5] ^ a[x + 10] ^ a[x + 15] ^ a[x + 20];
        for (int x = 0; x < 5; x++)                                                  /* θ */
            for (int y = 0; y < 25; y += 5) a[x + y] ^= c[(x + 4) % 5] ^ ROL(c[(x + 1) % 5], 1);
        for (int x = 0; x < 5; x++)                                                  /* ρ, π */
            for (int y = 0; y < 5; y++) b[y + 5 * ((2 * x + 3 * y) % 5)] = ROL(a[x + 5 * y], RHO[x + 5 * y]);
        for (int y = 0; y < 25; y += 5)                                              /* χ */
            for (int x = 0; x < 5; x++) a[x + y] = b[x + y] ^ (~b[(x + 1) % 5 + y] & b[(x + 2) % 5 + y]);
        a[0] ^= RC[r];                                                               /* ι */
    }
}

static void keccak256(uint8_t out[32], const uint8_t *msg, size_t len) {
    uint64_t a[25] = {0};
    uint8_t blk[136];
    for (;;) {
        size_t k = len < 136 ? len : 136;
        memset(blk, 0, 136);
        memcpy(blk, msg, k);
        if (k < 136) { blk[k] ^= 0x01; blk[135] ^= 0x80; }
        for (int i = 0; i < 136; i++) a[i / 8] ^= (uint64_t)blk[i] << (8 * (i % 8));
        keccak_f(a);
        if (k < 136) break;
        msg += 136; len -= 136;
    }
    for (int i = 0; i < 32; i++) out[i] = (uint8_t)(a[i / 8] >> (8 * (i % 8)));
}

/* ---- the contract's statements (RecursionFast/Contract/Relation.lean) ------------------------- */
static void put64(uint8_t *p, uint64_t x) { for (int i = 0; i < 8; i++) p[i] = (uint8_t)(x >> (8 * i)); }
static uint64_t get64(const uint8_t *p) { uint64_t x = 0; for (int i = 7; i >= 0; i--) x = x << 8 | p[i]; return x; }

static void chain_end(uint8_t d[32], const uint8_t s[32], uint64_t n) {
    uint8_t b[33];
    memcpy(d, s, 32);
    for (uint64_t k = 0; k < n; k++) { b[0] = 0x43; memcpy(b + 1, d, 32); keccak256(d, b, 33); }
}
static void leaf_stmt(uint8_t c[32], const uint8_t h[32], uint64_t n) {
    uint8_t b[41]; b[0] = 0x4C; memcpy(b + 1, h, 32); put64(b + 33, n); keccak256(c, b, 41);
}
static void node_stmt(uint8_t c[32], const uint8_t a[32], const uint8_t b2[32]) {
    uint8_t b[65]; b[0] = 0x4E; memcpy(b + 1, a, 32); memcpy(b + 33, b2, 32); keccak256(c, b, 65);
}

