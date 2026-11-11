/* Tests of the chain kernels against the baseline's portable Keccak (ref_keccak.h) and, with "vectors", the
 * values an independent Python implementation (test_vectors.py) checks.
 *   test_keccak [all]            every kernel this CPU can run; the others are reported as not tested
 *   test_keccak NAME             that kernel only; fails if this CPU cannot run it
 *   test_keccak available        the names of the kernels this CPU can run, one line
 *   test_keccak vectors          print vectors for test_vectors.py (every kernel this CPU can run)
 *   test_keccak bench [NAME]     ns per permutation of a sequential chain (pin it yourself)
 * TK_QUICK=1 cuts the chain counts and lengths (for emulators).
 */
#define _GNU_SOURCE
#include <stdio.h>
#include <stdlib.h>
#include "ref_keccak.h"
#include "chain.h"

static uint64_t rng_s = 0x9E3779B97F4A7C15ull;
static uint64_t rnd(void) { rng_s ^= rng_s << 13; rng_s ^= rng_s >> 7; rng_s ^= rng_s << 17; return rng_s * 0x2545F4914F6CDD1Dull; }
static void rndbytes(uint8_t *p, size_t n) { for (size_t i = 0; i < n; i++) p[i] = (uint8_t)(rnd() >> 24); }
static int fails, quick;
#define CHECK(c, ...) do { if (!(c)) { fails++; printf("FAIL: " __VA_ARGS__); printf("\n"); } } while (0)
static void hex(const uint8_t *p, size_t n) { for (size_t i = 0; i < n; i++) printf("%02x", p[i]); }

/* The whole permutation, where a kernel has one: scalar and bmi compute every lane, avx512 the digest
   (lanes 0..3); avx512vl exists only as a chain, whose tests below cover it. */
static int permute(int k, uint64_t st[25]) {
    switch (k) {
    case K_SCALAR: keccak_f_scalar(st); return 25;
    case K_BMI: keccak_f_bmi(st); return 25;
    case K_AVX512: keccak_f_digest_avx512(st); return 4;
    }
    return 0;
}

static void test_impl(int k) {
    printf("%-8s", k_name[k]); fflush(stdout);
    /* 1. the permutation on random full states (not only the chain's padded shape) */
    int lanes = 0;
    for (int t = 0; t < (quick ? 500 : 20000); t++) {
        uint64_t a[25], b[25];
        for (int i = 0; i < 25; i++) a[i] = b[i] = rnd();
        if (t == 0) for (int i = 0; i < 25; i++) a[i] = b[i] = 0;
        if (t == 1) for (int i = 0; i < 25; i++) a[i] = b[i] = ~0ull;
        keccak_f(a);
        lanes = permute(k, b);
        if (!lanes) break;
        CHECK(!memcmp(a, b, 8 * lanes), "%s: permutation mismatch on state %d", k_name[k], t);
        if (fails) return;
    }
    printf(lanes ? " permutation ok;" : " (chain only);"); fflush(stdout);
    /* 2. chains of n = 0, 1, 2, 3 and random n up to 300, from random starts */
    for (int t = 0; t < (quick ? 300 : 20000); t++) {
        uint8_t s[32], w[32], g[32];
        rndbytes(s, 32);
        uint64_t n = t < 4 ? (uint64_t)t : rnd() % 300;
        chain_end(w, s, n); k_fn[k](g, s, n);
        CHECK(!memcmp(w, g, 32), "%s: chain mismatch at n = %llu", k_name[k], (unsigned long long)n);
        if (fails) return;
    }
    printf(" short chains ok;"); fflush(stdout);
    /* 3. long chains: at least 1e5 steps from random starts (the chain's lanes are re-packed every step,
       so an error in the packing shows up as a divergence that grows with n) */
    for (int t = 0; t < (quick ? 1 : 12); t++) {
        uint8_t s[32], w[32], g[32];
        rndbytes(s, 32);
        uint64_t n = quick ? 5000 : 100000 + (t == 0 ? 0 : rnd() % 50000);
        chain_end(w, s, n); k_fn[k](g, s, n);
        CHECK(!memcmp(w, g, 32), "%s: long chain mismatch, n = %llu", k_name[k], (unsigned long long)n);
        if (fails) return;
    }
    printf(quick ? " a 5000-step chain ok" : " 1e5-step chains ok");
    /* 4. two chains in one call (step 1), of equal and unequal lengths, each against its own reference */
    if (k_two(k)) {
        static const uint64_t ns[][2] = {{0, 0}, {0, 5}, {7, 0}, {1, 1}, {300, 299}, {1000, 3000}, {131073, 100000}};
        for (size_t t = 0; t < sizeof ns / sizeof ns[0]; t++) {
            uint8_t sa[32], sb[32], wa[32], wb[32], ga[32], gb[32];
            rndbytes(sa, 32); rndbytes(sb, 32);
            chain_end(wa, sa, ns[t][0]); chain_end(wb, sb, ns[t][1]);
            chain_two(k, ga, sa, ns[t][0], gb, sb, ns[t][1]);
            CHECK(!memcmp(wa, ga, 32) && !memcmp(wb, gb, 32), "%s: two chains mismatch at n = %llu, %llu", k_name[k],
                  (unsigned long long)ns[t][0], (unsigned long long)ns[t][1]);
            if (fails) return;
        }
        printf("; two-chain calls ok");
    }
    printf("\n");
}

static void vectors(void) {
    for (int k = 0; k < K_COUNT; k++) {
        if (!k_available(k)) continue;
        for (int j = 0; j < 4; j++) {
            static const uint64_t ns[4] = {0, 1, 2, 1000};
            uint8_t s[32], e[32], l[32];
            for (int i = 0; i < 32; i++) s[i] = (uint8_t)(i * 5 + j);
            k_fn[k](e, s, ns[j]);
            leaf_stmt(l, e, ns[j]);
            printf("chain %s %llu ", k_name[k], (unsigned long long)ns[j]); hex(s, 32); printf(" "); hex(e, 32); printf(" "); hex(l, 32); printf("\n");
        }
    }
    uint8_t a[32], b[32], c[32], e[32];
    for (int i = 0; i < 32; i++) { a[i] = (uint8_t)i; b[i] = (uint8_t)(255 - i); }
    node_stmt(c, a, b);
    printf("node "); hex(a, 32); printf(" "); hex(b, 32); printf(" "); hex(c, 32); printf("\n");
    keccak256(e, (const uint8_t *)"", 0);
    printf("empty "); hex(e, 32); printf("\n");
}

static void bench(const char *only) {
    uint8_t s[32], o[32];
    rndbytes(s, 32);
    for (int k = 0; k < K_COUNT; k++) {
        if (!k_available(k) || (only && strcmp(only, k_name[k]))) continue;
        double best = 1e30;
        for (int rep = 0; rep < 7; rep++) {
            uint64_t n = 200000;
            double t0 = now_ns();
            k_fn[k](o, s, n);
            double dt = (now_ns() - t0) / n;
            if (dt < best) best = dt;
        }
        printf("%-8s %.1f ns per permutation (best of 7 x 200000-step chains)\n", k_name[k], best);
    }
}

int main(int argc, char **argv) {
    const char *mode = argc > 1 ? argv[1] : "all";
    quick = getenv("TK_QUICK") != NULL;
    if (!strcmp(mode, "vectors")) { vectors(); return 0; }
    if (!strcmp(mode, "bench")) { bench(argc > 2 ? argv[2] : NULL); return 0; }
    if (!strcmp(mode, "available")) {
        for (int k = 0; k < K_COUNT; k++) if (k_available(k)) printf("%s ", k_name[k]);
        printf("\n");
        return 0;
    }
    uint8_t e[32];
    keccak256(e, (const uint8_t *)"", 0);
    static const uint8_t want[32] = {0xc5,0xd2,0x46,0x01,0x86,0xf7,0x23,0x3c,0x92,0x7e,0x7d,0xb2,0xdc,0xc7,0x03,0xc0,
                                     0xe5,0x00,0xb6,0x53,0xca,0x82,0x27,0x3b,0x7b,0xfa,0xd8,0x04,0x5d,0x85,0xa4,0x70};
    CHECK(!memcmp(e, want, 32), "keccak256(\"\")");
    printf("keccak256(\"\") = c5d24601...5d85a470: %s\n", fails ? "FAIL" : "ok");
    if (!strcmp(mode, "all")) {
        for (int k = 0; k < K_COUNT; k++)
            if (k_available(k)) test_impl(k);
            else printf("%-8s NOT TESTED: this CPU cannot run it\n", k_name[k]);
    } else {
        int k = k_find(mode);
        CHECK(k >= 0, "no kernel named %s", mode);
        if (k >= 0) {
            CHECK(k_available(k), "%s: this CPU cannot run it", mode);
            if (k_available(k)) test_impl(k);
        }
    }
    /* the timed choice hands out a kernel that is available and agrees with scalar */
    int s = chain_select_timed(2, 2000, NULL);
    CHECK(k_usable(s), "chain_select_timed chose %s, which is not usable", k_name[s]);
    printf(fails ? "FAILED (%d)\n" : "all passed\n", fails);
    return fails != 0;
}
