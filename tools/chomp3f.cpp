// Faster version of chomp3.cpp (same semantics, same output format): 3D Chomp on N^3 with
// infinite parts, relative caps cap_i = ALPHA * E_i + D, exact/heuristic tags.
// Cells are packed into 33-bit words (three 11-bit fields with a guard bit each), so the
// componentwise order test is one subtraction. Generator lists live in fixed arrays.
//
// Usage: chomp3f [-a ALPHA] [-d D] [-g 1] solve|moves|why "x,y,z ..." [DEPTH]
//   -g 1: cap every axis by ALPHA * max_i E_i + D (lengths often move between axes, e.g. in
//         mirror strategies, so per-axis caps can miss the right reply)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <string>
#include <vector>

using u64 = uint64_t;
static int ALPHA = 2, DSLACK = 6;
static bool GLOBALCAP = false;  // -g: cap every axis by ALPHA * (largest coordinate on any axis) + D
static const int INF = 1 << 29;
static const int MAXG = 96;

// fields occupy bits [0,10), [11,21), [22,32); bits 10, 21, 32 are guard bits
static const u64 GUARD = (1ull << 10) | (1ull << 21) | (1ull << 32);
// x is in the high field so that sorting packed cells is lexicographic in (x, y, z), as in chomp3
static inline u64 pack(int x, int y, int z) { return (u64)z | ((u64)y << 11) | ((u64)x << 22); }
static inline int fz(u64 p) { return p & 1023; }
static inline int fy(u64 p) { return (p >> 11) & 1023; }
static inline int fx(u64 p) { return (p >> 22) & 1023; }
static inline bool leq(u64 a, u64 b) { return (((b | GUARD) - a) & GUARD) == GUARD; }

struct Pos {
  int n;
  u64 g[MAXG];
};

static const int PERMS[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};

static inline u64 perm(u64 p, const int* q) {
  int c[3] = {fx(p), fy(p), fz(p)};
  return pack(c[q[0]], c[q[1]], c[q[2]]);
}

static void isort(u64* a, int n) {
  for (int i = 1; i < n; ++i) {
    u64 v = a[i];
    int j = i - 1;
    while (j >= 0 && a[j] > v) { a[j + 1] = a[j]; --j; }
    a[j + 1] = v;
  }
}

static void canon(Pos& p) {
  u64 best[MAXG], cur[MAXG];
  for (int i = 0; i < p.n; ++i) best[i] = p.g[i];
  isort(best, p.n);
  for (int k = 1; k < 6; ++k) {
    for (int i = 0; i < p.n; ++i) cur[i] = perm(p.g[i], PERMS[k]);
    isort(cur, p.n);
    if (std::lexicographical_compare(cur, cur + p.n, best, best + p.n))
      std::memcpy(best, cur, sizeof(u64) * p.n);
  }
  std::memcpy(p.g, best, sizeof(u64) * p.n);
}

static inline u64 mix(u64 x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdull; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ull; x ^= x >> 33;
  return x;
}

// open-addressing table: key (a,b) with b != 0; value in low 2 bits of stored b
struct Table {
  std::vector<u64> ka, kb;
  size_t mask = 0, used = 0;
  void init(size_t cap) { ka.assign(cap, 0); kb.assign(cap, 0); mask = cap - 1; used = 0; }
  void grow() {
    std::vector<u64> oa, ob;
    oa.swap(ka); ob.swap(kb);
    init((mask + 1) * 2);
    for (size_t i = 0; i < oa.size(); ++i)
      if (ob[i]) put(oa[i], ob[i] & ~3ull, ob[i] & 3);
  }
  bool get(u64 a, u64 b, int& v) const {
    size_t i = (a ^ (b * 0x9E3779B97F4A7C15ull)) & mask;
    while (kb[i]) {
      if (ka[i] == a && (kb[i] & ~3ull) == b) { v = kb[i] & 3; return true; }
      i = (i + 1) & mask;
    }
    return false;
  }
  void put(u64 a, u64 b, int v) {
    if ((used + 1) * 10 > (mask + 1) * 7) grow();
    size_t i = (a ^ (b * 0x9E3779B97F4A7C15ull)) & mask;
    while (kb[i]) {
      if (ka[i] == a && (kb[i] & ~3ull) == b) { kb[i] = b | v; return; }
      i = (i + 1) & mask;
    }
    ka[i] = a; kb[i] = b | v; ++used;
  }
} memo;

static void keyOf(const Pos& p, u64& a, u64& b) {
  a = 0x1234567ull + p.n; b = 0x89abcdefull ^ ((u64)p.n << 40);
  for (int i = 0; i < p.n; ++i) { a = mix(a ^ p.g[i]); b = mix(b + p.g[i] * 0x2545F4914F6CDD1Dull); }
  b = (b << 2) | 4;  // nonzero, low 2 bits free
}

static void child(const Pos& p, u64 m, Pos& c) {
  c.n = 0;
  for (int i = 0; i < p.n; ++i)
    if (!leq(m, p.g[i])) c.g[c.n++] = p.g[i];
  if (c.n >= MAXG) { std::fprintf(stderr, "too many generators\n"); std::exit(1); }
  c.g[c.n++] = m;
  canon(c);
}

static void caps(const Pos& p, int cap[3], bool& truncated) {
  int nb[3] = {INF, INF, INF}, e[3] = {0, 0, 0};
  for (int i = 0; i < p.n; ++i) {
    int c[3] = {fx(p.g[i]), fy(p.g[i]), fz(p.g[i])};
    for (int k = 0; k < 3; ++k) e[k] = std::max(e[k], c[k]);
    if (c[1] == 0 && c[2] == 0) nb[0] = std::min(nb[0], c[0]);
    if (c[0] == 0 && c[2] == 0) nb[1] = std::min(nb[1], c[1]);
    if (c[0] == 0 && c[1] == 0) nb[2] = std::min(nb[2], c[2]);
  }
  truncated = false;
  int eg = std::max(e[0], std::max(e[1], e[2]));
  for (int k = 0; k < 3; ++k) {
    int c = ALPHA * (GLOBALCAP ? eg : e[k]) + DSLACK;
    if (c > 1000) c = 1000;
    if (nb[k] - 1 <= c) c = nb[k] - 1; else truncated = true;
    cap[k] = c;
  }
}

static inline int colHeight(const Pos& p, int x, int y) {
  int h = INF;
  for (int i = 0; i < p.n; ++i)
    if (fx(p.g[i]) <= x && fy(p.g[i]) <= y) h = std::min(h, fz(p.g[i]));
  return h;
}

static long long nodes = 0;

static int solve(const Pos& p) {  // bit1 = N, bit2 = exact
  u64 a, b;
  keyOf(p, a, b);
  int v;
  if (memo.get(a, b, v)) return v;
  ++nodes;
  if ((nodes & ((1 << 22) - 1)) == 0) { std::fprintf(stderr, "  ... %lld positions\n", nodes); }
  int cap[3];
  bool truncated;
  caps(p, cap, truncated);
  bool win = false, winExact = false, allExact = true;
  Pos c;
  for (int x = 0; x <= cap[0] && !win; ++x) {
    if (colHeight(p, x, 0) == 0) break;
    for (int y = 0; y <= cap[1] && !win; ++y) {
      int h = colHeight(p, x, y);
      if (h == 0) break;
      for (int z = std::min(h - 1, cap[2]); z >= 0 && !win; --z) {
        if (x == 0 && y == 0 && z == 0) continue;
        child(p, pack(x, y, z), c);
        int r = solve(c);
        if (!(r & 1)) { win = true; winExact = r & 2; }
        else if (!(r & 2)) allExact = false;
      }
    }
  }
  int res = win ? (1 | (winExact ? 2 : 0)) : ((!truncated && allExact) ? 2 : 0);
  memo.put(a, b, res);
  return res;
}

static Pos parse(const char* s) {
  std::vector<u64> g;
  const char* q = s;
  while (*q) {
    while (*q == ' ' || *q == ';') ++q;
    if (!*q) break;
    int x, y, z, n;
    if (std::sscanf(q, "%d,%d,%d%n", &x, &y, &z, &n) != 3) { std::fprintf(stderr, "bad list\n"); std::exit(1); }
    g.push_back(pack(x, y, z));
    q += n;
  }
  Pos p;
  p.n = 0;
  for (size_t i = 0; i < g.size(); ++i) {
    bool dom = false;
    for (size_t j = 0; j < g.size(); ++j)
      if (j != i && leq(g[j], g[i]) && (g[j] != g[i] || j < i)) dom = true;
    if (!dom) p.g[p.n++] = g[i];
  }
  return p;
}

static std::string show(const Pos& p) {
  std::string s;
  for (int i = 0; i < p.n; ++i) {
    char buf[64];
    std::snprintf(buf, sizeof buf, "%s(%d,%d,%d)", s.empty() ? "" : " ", fx(p.g[i]), fy(p.g[i]), fz(p.g[i]));
    s += buf;
  }
  return s.empty() ? "{}" : s;
}

static void explain(const Pos& p, int indent, int depth) {
  int r = solve(p);
  std::printf("%*s%s : %s%s\n", indent, "", show(p).c_str(), (r & 1) ? "N" : "P", (r & 2) ? "" : "?");
  if (depth <= 0) return;
  int cap[3];
  bool truncated;
  caps(p, cap, truncated);
  Pos c;
  for (int x = 0; x <= cap[0]; ++x)
    for (int y = 0; y <= cap[1]; ++y) {
      int h = colHeight(p, x, y);
      for (int z = std::min(h, cap[2] + 1) - 1; z >= 0; --z) {
        if (x == 0 && y == 0 && z == 0) continue;
        child(p, pack(x, y, z), c);
        int rc = solve(c);
        if ((r & 1) && !(rc & 1)) {
          std::printf("%*s  move (%d,%d,%d) ->\n", indent, "", x, y, z);
          explain(c, indent + 4, depth - 1);
          return;
        }
        if (!(r & 1)) {
          std::printf("%*s  option (%d,%d,%d) ->\n", indent, "", x, y, z);
          explain(c, indent + 4, depth - 1);
        }
      }
    }
}

static int g_argc;
static char** g_argv;

static void* run(void*) {
  int i = 1;
  while (i + 1 < g_argc && g_argv[i][0] == '-') {
    if (!std::strcmp(g_argv[i], "-a")) ALPHA = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-d")) DSLACK = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-g")) { GLOBALCAP = std::atoi(g_argv[i + 1]) != 0; }
    else break;
    i += 2;
  }
  if (i + 1 >= g_argc) { std::fprintf(stderr, "usage: chomp3f [-a A] [-d D] solve|moves|why \"x,y,z ...\" [DEPTH]\n"); std::exit(1); }
  memo.init(1 << 20);
  const char* mode = g_argv[i];
  Pos p = parse(g_argv[i + 1]);
  Pos pc = p;
  canon(pc);
  if (!std::strcmp(mode, "solve")) {
    int r = solve(pc);
    std::printf("%s : %s %s   [alpha=%d d=%d, %lld positions]\n", show(p).c_str(), (r & 1) ? "N" : "P",
                (r & 2) ? "exact" : "heuristic", ALPHA, DSLACK, nodes);
  } else if (!std::strcmp(mode, "moves")) {
    int cap[3];
    bool truncated;
    caps(p, cap, truncated);
    std::printf("%s : winning moves (caps %d,%d,%d):", show(p).c_str(), cap[0], cap[1], cap[2]);
    std::fflush(stdout);
    Pos c;
    for (int x = 0; x <= cap[0]; ++x)
      for (int y = 0; y <= cap[1]; ++y) {
        int h = colHeight(p, x, y);
        for (int z = 0; z < std::min(h, cap[2] + 1); ++z) {
          if (x == 0 && y == 0 && z == 0) continue;
          child(p, pack(x, y, z), c);
          int r = solve(c);
          if (!(r & 1)) { std::printf(" (%d,%d,%d)%s", x, y, z, (r & 2) ? "" : "?"); std::fflush(stdout); }
        }
      }
    std::printf("   [alpha=%d d=%d, %lld positions]  (? = heuristic)\n", ALPHA, DSLACK, nodes);
  } else if (!std::strcmp(mode, "why")) {
    int depth = (i + 2 < g_argc) ? std::atoi(g_argv[i + 2]) : 1;
    explain(pc, 0, depth);
  }
  std::fflush(stdout);
  return nullptr;
}

int main(int argc, char** argv) {
  g_argc = argc;
  g_argv = argv;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)4 << 30);
  pthread_t t;
  pthread_create(&t, &attr, run, nullptr);
  pthread_join(t, nullptr);
  return 0;
}
