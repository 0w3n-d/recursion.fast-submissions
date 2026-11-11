/*
 * The prover of this entry (harness/PROVER.md of the core is its interface).  Its proofs are the
 * witness-baseline entry's, byte for byte, apart from the service's signatures: the core library's
 * witness-sending argument, in the same encoding (src/ref_prover.c is that prover, the tests' reference).
 * What changes is how fast they are made:
 *
 *   - the chain d <- Keccak-256(0x43 || d) runs on the fastest kernel this CPU has (chain.h), timed by
 *     `prover setup` (untimed) and read back by every request, which re-checks it before `ready`;
 *   - step 1's two chains run in one thread with the avx512vl kernel (one per qword), else on two threads;
 *   - nothing but the chain's end depends on the chain: the proof is encoded, the empty-trace SIGNs are
 *     made and the file is written while the chain runs (a signature covers the trace's digest, not pi, so
 *     it does not depend on the chain), and only the two child statements of the node (2 x 32 bytes of its
 *     header) are patched in with pwrite when the chain ends, before the rename to proof.bin;
 *   - every thread is made before `ready` and released at `go`; where the CPU topology is readable, the
 *     helpers run off the core the chain thread is on at `ready`.
 *
 *   prover setup DIR      times the kernels; DIR/keccak names the fastest (best effort: a request whose
 *                         DIR/keccak is missing or names an unusable kernel times them itself)
 *   prover first DIR      ready/go handshake; DIR/chainA.json, DIR/chainB.json -> DIR/proof.bin, a signed
 *                         proof of nodeStmt (leaf A) (leaf B)
 *   prover step DIR       ready/go handshake; DIR/prev.stmt, DIR/prev.bin, DIR/chain.json -> DIR/proof.bin,
 *                         a signed proof of nodeStmt prev (leaf)
 *
 * For tests: RF_KECCAK=NAME forces a kernel (a request fails if it is not usable here), and RF_KECCAK_LOG
 * prints the kernel and how it was chosen to stderr.  prover/prover.s is `gcc -S -O2` of this file,
 * passed through the core's harness/tools/asm-compat.py; src/regen.sh regenerates it.
 */
#define _GNU_SOURCE
#include <pthread.h>
#include <sched.h>
#include <semaphore.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include "ref_keccak.h"
#include "chain.h"

/* ---- buffers and files ----------------------------------------------------------------------- */
typedef struct { uint8_t *p; size_t n, cap; } buf;
static void die(const char *m) { fprintf(stderr, "prover: %s\n", m); exit(1); }
static void reserve(buf *b, size_t extra) {
    if (b->n + extra + 1 <= b->cap) return;
    size_t c = b->cap ? b->cap : 4096;
    while (c < b->n + extra + 1) c *= 2;
    b->p = realloc(b->p, c); if (!b->p) die("out of memory");
    b->cap = c;
}
static void app(buf *b, const void *x, size_t n) { reserve(b, n); memcpy(b->p + b->n, x, n); b->n += n; }
static void app64(buf *b, uint64_t x) { uint8_t t[8]; put64(t, x); app(b, t, 8); }
static buf readfile(const char *path) {
    buf b = {0, 0, 0};
    int fd = open(path, O_RDONLY); if (fd < 0) die(path);
    struct stat st; if (fstat(fd, &st)) die(path);
    reserve(&b, (size_t)st.st_size + 1);
    for (;;) {
        if (b.n + 1 == b.cap) reserve(&b, 65536);         /* the file grew after fstat */
        ssize_t k = read(fd, b.p + b.n, b.cap - b.n - 1);
        if (k < 0) die(path);
        if (k == 0) break;
        b.n += (size_t)k;
    }
    close(fd); b.p[b.n] = 0; return b;
}
static void writeall(int fd, const uint8_t *p, size_t n, const char *what) {
    while (n) { ssize_t k = write(fd, p, n); if (k <= 0) die(what); p += k; n -= (size_t)k; }
}
static int unhex(uint8_t *out, const char *s, size_t n) {
    for (size_t i = 0; i < n; i++) {
        unsigned v; if (sscanf(s + 2 * i, "%2x", &v) != 1) return -1; out[i] = (uint8_t)v;
    }
    return 0;
}

/* ---- the oracle service: SIGN of the empty trace --------------------------------------------- */
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
    buf b = {0, 0, 0}; app64(&b, 0); app(&b, s, 32); app64(&b, n); return b;
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
/* The node's π with its two child statements left zero (the caller patches them, at NODE_C1 and
   NODE_C2 in π), carrying the two children's files. */
#define NODE_C1 8
#define NODE_C2 40
static buf ws_node(buf f1, buf f2) {
    uint8_t z[32] = {0};
    buf b = {0, 0, 0};
    reserve(&b, 72 + f1.n + f2.n + 64);         /* the usual size: both files, re-padded */
    app64(&b, 1); app(&b, z, 32); app(&b, z, 32);
    app_signed_words(&b, f1); app_signed_words(&b, f2); return b;
}
/* The signed-proof file of a π with the empty trace, signed by one SIGN. */
static buf signed_file(buf pi) {
    uint8_t sig[SIG_WIRE];
    sign_empty(sig);
    buf f = {0, 0, 0};
    reserve(&f, pi.n + 8 + 8 + 8 + SIG_WIRE);
    app64(&f, pi.n); app(&f, pi.p, pi.n);
    app64(&f, 0);                                       /* the trace: no query */
    uint32_t idx = sig[0] | sig[1] << 8 | sig[2] << 16 | (uint32_t)sig[3] << 24;
    app64(&f, idx); app(&f, sig + 4, SIG_WIRE - 4);
    return f;
}
/* In the signed file of a node, the offset of π's byte i is 8 + i. */
#define FILE_PI(i) (8 + (i))

/* ---- the chain ---------------------------------------------------------------------------------- */
static int impl;   /* the index into k_fn, chosen before `ready` */

typedef struct { uint8_t start[32]; uint64_t n; uint8_t stmt[32]; } chain_job;
/* A chain file {"n": N, "start": "HEX"}. */
static void parse_chain_file(const char *path, chain_job *c) {
    buf j = readfile(path);
    char *p = strstr((char *)j.p, "\"n\":"), *q = strstr((char *)j.p, "\"start\":");
    if (!p || !q) die(path);
    q = strchr(q + 8, '"'); if (!q || unhex(c->start, q + 1, 32)) die(path);
    c->n = strtoull(p + 4, NULL, 10);
    free(j.p);
}
/* The leaf statement of the chain: its end, hashed. */
static void run_chain(chain_job *c) {
    uint8_t h[32];
    k_fn[impl](h, c->start, c->n);
    leaf_stmt(c->stmt, h, c->n);
}
/* Step 1's two chains in this thread (k_two(impl)). */
static void run_two(chain_job *a, chain_job *b) {
    uint8_t ha[32], hb[32];
    chain_two(impl, ha, a->start, a->n, hb, b->start, b->n);
    leaf_stmt(a->stmt, ha, a->n);
    leaf_stmt(b->stmt, hb, b->n);
}

/* ---- threads, made before `ready` and released at `go` -------------------------------------------- */
/* With the CPU topology readable (Linux sysfs), the helpers may run only on CPUs outside the core that the
   main thread (the chain) is on at `ready`, so that no helper starts as the chain's SMT sibling; the main
   thread itself stays free to move.  Without the topology, or if a helper cannot be given that mask, the
   scheduler places it. */
static cpu_set_t core_set, rest_set;
static int placed;
static void place_helpers(void) {
    cpu_set_t all;
    char path[96], s[256];
    int c = sched_getcpu();
    if (c < 0 || sched_getaffinity(0, sizeof all, &all)) return;
    snprintf(path, sizeof path, "/sys/devices/system/cpu/cpu%d/topology/thread_siblings_list", c);
    FILE *f = fopen(path, "r");
    if (!f) return;
    char *got = fgets(s, sizeof s, f);
    fclose(f);
    if (!got) return;
    CPU_ZERO(&core_set);
    for (char *p = s;;) {                       /* "13,29" or "0-1" */
        char *e;
        long a = strtol(p, &e, 10), b = a;
        if (e == p || a < 0) return;
        if (*e == '-') {
            p = e + 1; b = strtol(p, &e, 10);
            if (e == p || b < a) return;
        }
        for (long i = a; i <= b && i < CPU_SETSIZE; i++) CPU_SET((int)i, &core_set);
        if (*e != ',') break;
        p = e + 1;
    }
    CPU_AND(&core_set, &core_set, &all);
    if (!CPU_ISSET(c, &core_set)) return;
    CPU_XOR(&rest_set, &all, &core_set);
    if (!CPU_COUNT(&rest_set)) return;
    placed = 1;
}

/* A helper thread: it waits for `go`, then runs fn(arg). */
typedef struct { sem_t go; void *(*fn)(void *); void *arg; pthread_t t; } helper;
static void *helper_main(void *arg) {
    helper *h = arg;
    while (sem_wait(&h->go)) {}
    return h->fn(h->arg);
}
static void helper_start(helper *h, void *(*fn)(void *), void *arg) {
    pthread_attr_t at;
    h->fn = fn; h->arg = arg;
    if (sem_init(&h->go, 0, 0) || pthread_attr_init(&at)) die("thread setup");
    int pin = placed && !pthread_attr_setaffinity_np(&at, sizeof rest_set, &rest_set);
    if (pthread_create(&h->t, pin ? &at : NULL, helper_main, h) && (!pin || pthread_create(&h->t, NULL, helper_main, h)))
        die("pthread_create");                  /* placed, then unplaced */
    pthread_attr_destroy(&at);
}
static void helper_go(helper *h) { if (sem_post(&h->go)) die("sem_post"); }
static void helper_join(helper *h) { pthread_join(h->t, NULL); }

/* ---- the proof, prepared while the chains run ----------------------------------------------------- */
typedef struct {
    int first;                   /* 1: two chains (first), 0: prev + one chain (step) */
    int fd;                      /* proof.bin.tmp, written whole except the two statements (zeros) */
    uint8_t c1[32];              /* step: prev.stmt */
} prep;

/* The buffers are not freed: the process ends with the request. */
static void read_stmt(uint8_t c[32], const char *path);
static void *prep_thread(void *arg) {
    prep *p = arg;
    buf f1, f2;
    if (p->first) {
        chain_job a, b;
        parse_chain_file("chainA.json", &a); parse_chain_file("chainB.json", &b);
        f1 = signed_file(ws_leaf(a.start, a.n)); f2 = signed_file(ws_leaf(b.start, b.n));
    } else {
        chain_job b;
        parse_chain_file("chain.json", &b);
        read_stmt(p->c1, "prev.stmt");
        f1 = readfile("prev.bin");
        f2 = signed_file(ws_leaf(b.start, b.n));
    }
    buf out = signed_file(ws_node(f1, f2));
    p->fd = open("proof.bin.tmp", O_WRONLY | O_CREAT | O_TRUNC, 0644);
    if (p->fd < 0) die("proof.bin.tmp");
    writeall(p->fd, out.p, out.n, "proof.bin.tmp");
    return NULL;
}
static void *chain_thread(void *arg) {
    chain_job *c = arg;
    parse_chain_file("chainB.json", c);
    run_chain(c);
    return NULL;
}

/* The kernel for this request (untimed): RF_KECCAK, else the setup's choice, else a timed one. */
static void choose_kernel(void) {
    char setup[4096];
    const char *how, *d = getenv("RF_SETUP");
    if (d) snprintf(setup, sizeof setup, "%s/keccak", d);
    impl = chain_select(getenv("RF_KECCAK"), d ? setup : NULL, &how);
    if (impl < 0) die("RF_KECCAK names no kernel usable here");
    if (getenv("RF_KECCAK_LOG")) fprintf(stderr, "prover: keccak %s (%s)\n", k_name[impl], how);
}

/* Make the helpers (untimed), then `ready`, then wait for `go` and release them. */
static void handshake(helper *hs, int nh) {
    char line[64];
    place_helpers();
    for (int i = 0; i < nh; i++) helper_start(&hs[i], hs[i].fn, hs[i].arg);
    printf("ready\n"); fflush(stdout);
    if (!fgets(line, sizeof line, stdin) || strncmp(line, "go", 2)) die("no go");
    for (int i = 0; i < nh; i++) helper_go(&hs[i]);
}

/* Patches the node's two child statements into the written file and publishes it. */
static void finish_proof(prep *p, const uint8_t c1[32], const uint8_t c2[32]) {
    if (pwrite(p->fd, c1, 32, FILE_PI(NODE_C1)) != 32 || pwrite(p->fd, c2, 32, FILE_PI(NODE_C2)) != 32) die("proof.bin.tmp");
    if (close(p->fd) || rename("proof.bin.tmp", "proof.bin")) die("proof.bin");
}

static void read_stmt(uint8_t c[32], const char *path) {
    buf b = readfile(path);
    if (b.n < 64 || unhex(c, (char *)b.p, 32)) die(path);
    free(b.p);
}

static int mode_setup(void) {
    int k = chain_select_timed(11, 1 << 16, stdout);
    FILE *f = fopen("keccak", "w");
    int ok = f && fprintf(f, "%s\n", k_name[k]) > 0;
    if (f && fclose(f)) ok = 0;
    printf(ok ? "keccak chosen: %s\n" : "keccak: cannot write DIR/keccak (requests will time the kernels): %s\n", k_name[k]);
    return 0;
}

static int mode_first(void) {
    prep p = {.first = 1};
    chain_job a, b;
    helper hs[2] = {{.fn = prep_thread, .arg = &p}, {.fn = chain_thread, .arg = &b}};
    choose_kernel();
    int two = k_two(impl);                       /* both chains in this thread, or chain B on a helper */
    handshake(hs, two ? 1 : 2);
    parse_chain_file("chainA.json", &a);
    if (two) { parse_chain_file("chainB.json", &b); run_two(&a, &b); }
    else { run_chain(&a); helper_join(&hs[1]); }
    helper_join(&hs[0]);
    finish_proof(&p, a.stmt, b.stmt);
    printf("done\n"); fflush(stdout);
    return 0;
}

static int mode_step(void) {
    prep p = {.first = 0};
    chain_job c;
    helper hs[1] = {{.fn = prep_thread, .arg = &p}};
    choose_kernel();
    handshake(hs, 1);
    parse_chain_file("chain.json", &c);
    run_chain(&c);
    helper_join(&hs[0]);
    finish_proof(&p, p.c1, c.stmt);
    printf("done\n"); fflush(stdout);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) die("usage: prover setup|first|step DIR");
    if (chdir(argv[2])) die("cannot enter DIR");
    if (!strcmp(argv[1], "setup")) return mode_setup();
    if (!strcmp(argv[1], "first")) return mode_first();
    if (!strcmp(argv[1], "step")) return mode_step();
    die("unknown mode");
    return 2;
}
