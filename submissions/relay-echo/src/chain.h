/* The hash chain d <- Keccak-256(0x43 || d), n times: the implementations and the run-time choice.
 *
 *   scalar    keccak_scalar.inc  baseline x86-64, lane complementing (any CPU; gen_scalar.py)
 *   bmi       keccak_lanes.inc   general registers, ANDN (BMI1) and RORX (BMI2) (gen_lanes.py)
 *   avx512    keccak_avx512.inc  AVX-512F, one state in five zmm rows
 *   avx512vl  keccak_vlasm.inc   AVX-512F/VL, one lane per xmm register (the upper qword runs a second chain)
 *   avx512vln keccak_vlasm.inc   the same with two of each row's chi outputs as VPANDNQ + VPXORQ (gen_vlasm.py)
 *
 * The translation unit is built for the baseline x86-64: only functions that carry a target attribute
 * contain BMI or AVX-512 instructions, and they are reached only through k_available(), which reads cpuid
 * (and, for AVX-512, xgetbv: the operating system must save the opmask and zmm state).  An instruction the
 * CPU lacks raises SIGILL before any result could be compared, so that check is the only guard; the
 * comparison against the scalar chain in chain_select() guards against a kernel that runs but is wrong.
 */
#include <cpuid.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <time.h>
#include "keccak_scalar.inc"
#include "keccak_lanes.inc"
#include "keccak_avx512.inc"
#include "keccak_vlasm.inc"

typedef void (*chain_fn)(uint8_t out[32], const uint8_t in[32], uint64_t n);
enum { K_SCALAR, K_BMI, K_AVX512, K_AVX512VL, K_AVX512VLN, K_COUNT };
static const char *const k_name[K_COUNT] = {"scalar", "bmi", "avx512", "avx512vl", "avx512vln"};
static const chain_fn k_fn[K_COUNT] = {chain_scalar, chain_bmi, chain_avx512, chain_avx512vl, chain_avx512vln};

static uint64_t xgetbv0(void) {
    uint32_t lo, hi;
    __asm__ volatile("xgetbv" : "=a"(lo), "=d"(hi) : "c"(0));
    return lo | (uint64_t)hi << 32;
}

/* Leaf 7's EBX if the CPU has leaf 7, else 0; *os512: the OS saves the opmask, ZMM_Hi256 and Hi16_ZMM
   state (OSXSAVE and AVX present, XCR0 & 0xE6 == 0xE6; xgetbv is reached only after OSXSAVE). */
static uint32_t cpu_leaf7_ebx(int *os512) {
    unsigned a, b, c, d;
    *os512 = 0;
    if (__get_cpuid_max(0, 0) < 7) return 0;
    __cpuid(1, a, b, c, d);
    if ((c & (1u << 27)) && (c & (1u << 28)) && (xgetbv0() & 0xE6) == 0xE6) *os512 = 1;
    __cpuid_count(7, 0, a, b, c, d);
    return b;
}

static int k_available(int k) {
    int os512;
    uint32_t b = cpu_leaf7_ebx(&os512);
    switch (k) {
    case K_SCALAR: return 1;
    case K_BMI: return (b >> 3 & 1) && (b >> 8 & 1);                     /* BMI1, BMI2 */
    case K_AVX512: return os512 && (b >> 16 & 1);                         /* AVX512F */
    case K_AVX512VL:
    case K_AVX512VLN: return os512 && (b >> 16 & 1) && (b >> 31 & 1);     /* AVX512F, AVX512VL */
    }
    return 0;
}

static double now_ns(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec * 1e9 + t.tv_nsec;
}

static int k_find(const char *name) {
    for (int k = 0; k < K_COUNT; k++)
        if (!strcmp(name, k_name[k])) return k;
    return -1;
}

/* Whether kernel k runs two chains for the price of one (chain_two). */
static int k_two(int k) { return k == K_AVX512VL || k == K_AVX512VLN; }

/* Two chains with kernel k (k_two(k)): both in one call for the shorter length, then the longer one alone. */
static void chain_two(int k, uint8_t ea[32], const uint8_t sa[32], uint64_t na, uint8_t eb[32],
                      const uint8_t sb[32], uint64_t nb) {
    uint64_t m = na < nb ? na : nb;
    void (*two)(uint8_t *, const uint8_t *, uint8_t *, const uint8_t *, uint64_t) =
        k == K_AVX512VLN ? chain2_avx512vln : chain2_avx512vl;
    two(ea, sa, eb, sb, m);
    if (na > m) k_fn[k](ea, ea, na - m);
    if (nb > m) k_fn[k](eb, eb, nb - m);
}

/* Whether kernel k is available here and agrees with the scalar chain on a fixed 300-step chain (and, for a
   two-chain kernel, on two different chains in one call). */
static int k_usable(int k) {
    uint8_t s[32], t[32], want[32], want2[32], got[32], got2[32];
    if (k < 0 || !k_available(k)) return 0;
    for (int i = 0; i < 32; i++) { s[i] = (uint8_t)(i * 37 + 11); t[i] = (uint8_t)(i * 59 + 3); }
    chain_scalar(want, s, 300);
    k_fn[k](got, s, 300);
    if (memcmp(got, want, 32)) return 0;
    if (!k_two(k)) return 1;
    chain_scalar(want2, t, 290);
    chain_two(k, got, s, 300, got2, t, 290);
    return !memcmp(got, want, 32) && !memcmp(got2, want2, 32);
}

/* The usable kernel that is fastest here: `rounds` rounds, each timing every usable kernel once on a chain
   of n steps, in an order that rotates between rounds; each kernel's best round decides (interference only
   slows a run).  scalar wins ties and is the answer when nothing else is usable.  log: NULL, or where to
   print each kernel's best time. */
static int chain_select_timed(int rounds, uint64_t n, FILE *log) {
    double best_t[K_COUNT];
    int ok[K_COUNT];
    uint8_t s[32], o[32];
    for (int i = 0; i < 32; i++) s[i] = (uint8_t)(i * 5 + 3);
    for (int k = 0; k < K_COUNT; k++) { ok[k] = k_usable(k); best_t[k] = 1e300; }
    for (int r = 0; r < rounds; r++)
        for (int j = 0; j < K_COUNT; j++) {
            int k = (r + j) % K_COUNT;
            if (!ok[k]) continue;
            double t0 = now_ns();
            k_fn[k](o, s, n);
            double dt = now_ns() - t0;
            if (dt < best_t[k]) best_t[k] = dt;
            s[0] ^= o[0];
        }
    int best = K_SCALAR;
    for (int k = 0; k < K_COUNT; k++) {
        if (log) {
            if (ok[k]) fprintf(log, "keccak %s %.1f ns per permutation\n", k_name[k], best_t[k] / n);
            else fprintf(log, "keccak %s not usable here\n", k_name[k]);
        }
        if (ok[k] && best_t[k] < best_t[best]) best = k;
    }
    return best;
}

/* The kernel for this request.  force (RF_KECCAK): a kernel's name, which must be usable (else -1: the
   caller fails, so that a test cannot pass on a path it did not run), or NULL / "auto".  For auto, the
   choice `prover setup` stored in setup_file, if it names a usable kernel; else a short timed choice.
   *how: "forced", "setup" or "timed". */
static int chain_select(const char *force, const char *setup_file, const char **how) {
    if (force && strcmp(force, "auto")) {
        int k = k_find(force);
        *how = "forced";
        return k_usable(k) ? k : -1;
    }
    if (setup_file) {
        FILE *f = fopen(setup_file, "r");
        char name[32] = {0};
        if (f) {
            int got = fscanf(f, "%31s", name) == 1;
            fclose(f);
            int k = got ? k_find(name) : -1;
            *how = "setup";
            if (k_usable(k)) return k;
        }
    }
    *how = "timed";
    return chain_select_timed(5, 5000, NULL);
}

