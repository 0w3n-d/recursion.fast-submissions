/* The tests' reference prover: a verbatim copy, below this comment, of the witness-baseline entry's
   src/prover.c (Apache-2.0, derived from the core's harness/toy-prover/toy.c). */
/*
 * The prover of the witness-baseline entry (harness/PROVER.md of the core is its interface).
 * Derived from the core's toy prover (harness/toy-prover/toy.c, Apache-2.0), with the smoke's
 * deliberately broken variants removed; the proving logic is unchanged.
 *
 * It proves with the core library's witness-sending argument (RecursionFast/Library/WitnessSending.lean):
 * the proof `π` is the witness itself, in the library's encoding (`encode`, below), and the verifier
 * makes no oracle query, so every trace is empty and every proof is signed by one `SIGN` request with
 * no items (service/PROTOCOL.md). It computes the public Keccak-256 chains and statements itself, to
 * name the children of a node. Its proofs grow with every step (a node carries its children whole).
 *
 *   prover setup DIR      nothing to set up
 *   prover first DIR      ready/go handshake; DIR/chainA.json, DIR/chainB.json -> DIR/proof.bin, a signed
 *                         proof of nodeStmt (leaf A) (leaf B)
 *   prover step DIR       ready/go handshake; DIR/prev.stmt, DIR/prev.bin, DIR/chain.json -> DIR/proof.bin,
 *                         a signed proof of nodeStmt prev (leaf)
 *
 * prover/prover.s is `gcc -S -O2` of this file, passed through the core's harness/tools/asm-compat.py;
 * src/regen.sh regenerates it byte for byte.
 */
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>

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

/* ---- buffers and files ----------------------------------------------------------------------- */
typedef struct { uint8_t *p; size_t n; } buf;
static void die(const char *m) { fprintf(stderr, "toy prover: %s\n", m); exit(1); }
static void app(buf *b, const void *x, size_t n) {
    b->p = realloc(b->p, b->n + n + 1); if (!b->p) die("out of memory");
    memcpy(b->p + b->n, x, n); b->n += n;
}
static void app64(buf *b, uint64_t x) { uint8_t t[8]; put64(t, x); app(b, t, 8); }
static buf readfile(const char *path) {
    buf b = {0, 0}; FILE *f = fopen(path, "rb"); if (!f) die(path);
    uint8_t t[65536]; size_t k;
    while ((k = fread(t, 1, sizeof t, f)) > 0) app(&b, t, k);
    fclose(f); return b;
}
static void writefile(const char *path, buf b) {
    char tmp[512]; snprintf(tmp, sizeof tmp, "%s.tmp", path);
    FILE *f = fopen(tmp, "wb"); if (!f || fwrite(b.p, 1, b.n, f) != b.n || fclose(f)) die(path);
    if (rename(tmp, path)) die(path);
}
static int unhex(uint8_t *out, const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) {
        unsigned v; if (sscanf(s + 2 * i, "%2x", &v) != 1) return -1; out[i] = (uint8_t)v;
    }
    return 0;
}

/* ---- the oracle service: one SIGN of the empty trace --------------------------------------- */
#define SIG_WIRE 4772   /* idx:u32 ‖ 133 × 32 ‖ 16 × 32 */
static int svc = -1;
static void connect_svc(void) {
    if (svc >= 0) return;
    const char *path = getenv("RF_ORACLE"); if (!path) die("RF_ORACLE unset");
    struct sockaddr_un a; memset(&a, 0, sizeof a); a.sun_family = AF_UNIX;
    strncpy(a.sun_path, path, sizeof a.sun_path - 1);
    svc = socket(AF_UNIX, SOCK_STREAM, 0);
    if (svc < 0 || connect(svc, (struct sockaddr *)&a, sizeof a)) die("cannot connect to the oracle service");
}
static void sign_empty(uint8_t sig[SIG_WIRE]) {
    connect_svc();
    uint8_t h[16] = {2};                      /* SIGN, count 0, body 0 */
    if (write(svc, h, 16) != 16) die("SIGN write");
    size_t got = 0;
    while (got < 16) { ssize_t k = read(svc, h + got, 16 - got); if (k <= 0) die("SIGN read"); got += k; }
    if (h[0] != 0 || get64(h + 8) != SIG_WIRE) die("SIGN refused");
    got = 0;
    while (got < SIG_WIRE) { ssize_t k = read(svc, sig + got, SIG_WIRE - got); if (k <= 0) die("SIGN read"); got += k; }
}

/* ---- the witness-sending proof and the signed-proof file (harness/FORMAT.md) ---------------- */
/* The library's witness-sending encoding (RecursionFast/Library/WitnessSending.lean, `encode`): the
   little-endian bytes of the extractor output words `witWords w` (Library/Words.lean):
     leaf: u64 0 ‖ start ‖ u64 n                                   (48 bytes)
     node: u64 1 ‖ c1 ‖ c2 ‖ signedWords p1 ‖ signedWords p2
   signedWords p = u64 |π| ‖ π padded to 8 ‖ u64 m ‖ (u64 |q| ‖ q padded to 8 ‖ a)* ‖ u64 idx ‖
   133 × 32 ots ‖ 16 × 32 path: the signed-proof file with π and every query zero-padded to a
   whole word. */
static const uint8_t ZERO8[8] = {0};
static buf ws_leaf(const uint8_t s[32], uint64_t n) {
    buf b = {0, 0}; app64(&b, 0); app(&b, s, 32); app64(&b, n); return b;
}
static void app_padded(buf *b, const uint8_t *p, size_t n) {
    app64(b, n); app(b, p, n); app(b, ZERO8, (8 - n % 8) % 8);
}
/* A signed-proof file, re-encoded as signedWords; dies on a malformed file. */
static void app_signed_words(buf *b, buf f) {
    size_t o = 0;
#define NEED(k) do { if ((k) > f.n - o) die("malformed child file"); } while (0)
    NEED(8); uint64_t np = get64(f.p + o); o += 8; NEED(np); app_padded(b, f.p + o, np); o += np;
    NEED(8); uint64_t m = get64(f.p + o); o += 8; app64(b, m);
    for (uint64_t i = 0; i < m; i++) {
        NEED(8); uint64_t nq = get64(f.p + o); o += 8; NEED(nq); app_padded(b, f.p + o, nq); o += nq;
        NEED(32); app(b, f.p + o, 32); o += 32;
    }
    NEED(8 + 149 * 32); app(b, f.p + o, 8 + 149 * 32); o += 8 + 149 * 32;
    if (o != f.n) die("trailing bytes in a child file");
#undef NEED
}
static buf ws_node(const uint8_t c1[32], const uint8_t c2[32], buf f1, buf f2) {
    buf b = {0, 0}; app64(&b, 1); app(&b, c1, 32); app(&b, c2, 32);
    app_signed_words(&b, f1); app_signed_words(&b, f2); return b;
}
static buf signed_file(buf pi) {
    uint8_t sig[SIG_WIRE];
    sign_empty(sig);
    buf f = {0, 0};
    app64(&f, pi.n); app(&f, pi.p, pi.n);
    app64(&f, 0);                                       /* the trace: no query */
    uint32_t idx = sig[0] | sig[1] << 8 | sig[2] << 16 | (uint32_t)sig[3] << 24;
    app64(&f, idx); app(&f, sig + 4, SIG_WIRE - 4);
    return f;
}

static buf prove_leaf(const uint8_t s[32], uint64_t n, uint8_t c[32]) {
    uint8_t h[32];
    chain_end(h, s, n);
    leaf_stmt(c, h, n);
    buf pi = ws_leaf(s, n), f = signed_file(pi);
    free(pi.p); return f;
}

/* ---- modes ------------------------------------------------------------------------------------- */
static void handshake(void) {
    char line[64];
    printf("ready\n"); fflush(stdout);
    if (!fgets(line, sizeof line, stdin) || strncmp(line, "go", 2)) die("no go");
}

/* A chain file {"n": N, "start": "HEX"}: its leaf's signed proof and statement. */
static buf prove_chain_file(const char *path, uint8_t c[32]) {
    buf j = readfile(path); app(&j, "", 1);
    char *p = strstr((char *)j.p, "\"n\":"), *q = strstr((char *)j.p, "\"start\":");
    if (!p || !q) die(path);
    uint8_t s[32];
    q = strchr(q + 8, '"'); if (!q || unhex(s, q + 1, 32)) die(path);
    buf f = prove_leaf(s, strtoull(p + 4, NULL, 10), c);
    free(j.p); return f;
}

static int mode_first(void) {
    handshake();
    uint8_t ca[32], cb[32];
    buf fa = prove_chain_file("chainA.json", ca), fb = prove_chain_file("chainB.json", cb);
    buf pi = ws_node(ca, cb, fa, fb);
    writefile("proof.bin", signed_file(pi));
    printf("done\n"); fflush(stdout);
    return 0;
}

static void read_stmt(uint8_t c[32], const char *path) {
    buf b = readfile(path); app(&b, "", 1);
    if (b.n < 65 || unhex(c, (char *)b.p, 32)) die(path);
    free(b.p);
}

int main(int argc, char **argv) {
    if (argc != 3) die("usage: prover setup|first|step DIR");
    if (chdir(argv[2])) die("cannot enter DIR");
    if (!strcmp(argv[1], "setup")) return 0;
    if (!strcmp(argv[1], "first")) return mode_first();
    if (!strcmp(argv[1], "step")) {
        handshake();
        uint8_t c1[32], c2[32];
        read_stmt(c1, "prev.stmt");
        buf f1 = readfile("prev.bin"), f2 = prove_chain_file("chain.json", c2);
        buf pi = ws_node(c1, c2, f1, f2);
        writefile("proof.bin", signed_file(pi));
        printf("done\n"); fflush(stdout);
        return 0;
    }
    die("unknown mode");
    return 2;
}
