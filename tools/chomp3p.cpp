// Depth-first proof-number search (df-pn) for 3D Chomp on N^3 with infinite parts.
//
// Same positions, moves and caps as chomp3f.cpp (positions are antichains of eaten cells,
// moves are capped at ALPHA * E + D, with E per axis or global with -g 1), but instead of
// plain depth-first search it uses df-pn (Nagai 2002) with a transposition table:
//   phi(n)   = cost to prove "player to move wins" = min over children of delta(child)
//   delta(n) = cost to prove "player to move loses" = sum over children of phi(child)
// The search always expands the child that looks cheapest to prove, so a quick win such as
// (1,0,0) from omega x L(1,1) is found even when it comes late in move order.
//
// Additions over chomp3f:
//   * a table of known exact P-positions (2 x omega and the infinite L-shape, in every
//     orientation) is seeded into the transposition table, so N results witnessed by them
//     are exact;
//   * children are ordered so that finite children and children with fewer unbounded axes
//     come first (they break ties between equal proof numbers);
//   * time limit (-t seconds); on timeout the result is "unknown".
//
// Exactness is as in chomp3f: N is exact when witnessed by an exact P child; P is exact
// when no move was cut off by the caps and every child is exactly N.
//
// Rod oracle (-r 1, default): a position with exactly one unbounded axis is converted to a rod
// position (cross-section over the two bounded axes, heights along the unbounded one) and
// decided by the rod solver in rod.h when its omega part has at most ORACLE_W = 2 cells besides
// the poison (-W; exact for one cell, a two-wide stalk) or its cross-section has at most 6 cells.
// Its answers are stored in the TT with their exact flag.
//
// Usage: chomp3p [-a ALPHA] [-d D] [-g 0|1] [-t SECONDS] [-r 0|1] solve|why|moves "x,y,z ..."
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <string>
#include <map>
#include <memory>
#include <unordered_map>
#include <vector>

#include "rod.h"

using u64 = uint64_t;
using u32 = uint32_t;
static int ALPHA = 1, DSLACK = 2;
static bool GLOBALCAP = true;
static double TLIMIT = 1e18;
static bool ORACLE = true;   // -r 0 disables the rod oracle
static int ORACLE_SMALL = 6; // rod shapes with at most this many cells are always handed over
static int ORACLE_W = 2;     // ... and so are rods with at most this many infinite cells besides the poison
static const int INFC = 1 << 29;
static const int MAXG = 96;
static const u32 INF = 0x3fffffff;

static const u64 GUARD = (1ull << 10) | (1ull << 21) | (1ull << 32);
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
    if (std::lexicographical_compare(cur, cur + p.n, best, best + p.n)) std::memcpy(best, cur, sizeof(u64) * p.n);
  }
  std::memcpy(p.g, best, sizeof(u64) * p.n);
}
static inline u64 mix(u64 x) {
  x ^= x >> 33; x *= 0xff51afd7ed558ccdull; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ull; x ^= x >> 33;
  return x;
}
static void keyOf(const Pos& p, u64& a, u64& b) {
  a = 0x1234567ull + p.n; b = 0x89abcdefull ^ ((u64)p.n << 40);
  for (int i = 0; i < p.n; ++i) { a = mix(a ^ p.g[i]); b = mix(b + p.g[i] * 0x2545F4914F6CDD1Dull); }
  b |= 1;  // nonzero
}

// ---- transposition table ----
struct Entry { u64 a, b; u32 phi, delta; u32 flags; };  // flags bit0: exact
struct TT {
  std::vector<Entry> t;
  size_t mask = 0, used = 0;
  void init(size_t cap) { t.assign(cap, Entry{0, 0, 0, 0, 0}); mask = cap - 1; used = 0; }
  Entry* find(u64 a, u64 b) {
    size_t i = (a ^ (b * 0x9E3779B97F4A7C15ull)) & mask;
    while (t[i].b) { if (t[i].a == a && t[i].b == b) return &t[i]; i = (i + 1) & mask; }
    return nullptr;
  }
  void grow() {
    std::vector<Entry> old; old.swap(t);
    init((mask + 1) * 2);
    for (auto& e : old) if (e.b) put(e.a, e.b, e.phi, e.delta, e.flags);
  }
  void put(u64 a, u64 b, u32 phi, u32 delta, u32 flags) {
    if ((used + 1) * 10 > (mask + 1) * 7) grow();
    size_t i = (a ^ (b * 0x9E3779B97F4A7C15ull)) & mask;
    while (t[i].b) {
      if (t[i].a == a && t[i].b == b) { t[i].phi = phi; t[i].delta = delta; t[i].flags = flags; return; }
      i = (i + 1) & mask;
    }
    t[i] = Entry{a, b, phi, delta, flags}; ++used;
  }
} tt;

static void child(const Pos& p, u64 m, Pos& c) {
  c.n = 0;
  for (int i = 0; i < p.n; ++i) if (!leq(m, p.g[i])) c.g[c.n++] = p.g[i];
  if (c.n >= MAXG) { std::fprintf(stderr, "too many generators\n"); std::exit(1); }
  c.g[c.n++] = m;
  canon(c);
}
static void bounds(const Pos& p, int nb[3], int e[3]) {
  nb[0] = nb[1] = nb[2] = INFC; e[0] = e[1] = e[2] = 0;
  for (int i = 0; i < p.n; ++i) {
    int c[3] = {fx(p.g[i]), fy(p.g[i]), fz(p.g[i])};
    for (int k = 0; k < 3; ++k) e[k] = std::max(e[k], c[k]);
    if (c[1] == 0 && c[2] == 0) nb[0] = std::min(nb[0], c[0]);
    if (c[0] == 0 && c[2] == 0) nb[1] = std::min(nb[1], c[1]);
    if (c[0] == 0 && c[1] == 0) nb[2] = std::min(nb[2], c[2]);
  }
}
static void caps(const Pos& p, int cap[3], bool& truncated) {
  int nb[3], e[3];
  bounds(p, nb, e);
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
  int h = INFC;
  for (int i = 0; i < p.n; ++i) if (fx(p.g[i]) <= x && fy(p.g[i]) <= y) h = std::min(h, fz(p.g[i]));
  return h;
}
static int unboundedAxes(const Pos& p) {
  int nb[3], e[3];
  bounds(p, nb, e);
  return (nb[0] == INFC) + (nb[1] == INFC) + (nb[2] == INFC);
}

struct Child { u64 m, a, b; int score; };

static bool genChildren(const Pos& p, std::vector<Child>& out) {
  int cap[3];
  bool truncated;
  caps(p, cap, truncated);
  out.clear();
  Pos c;
  for (int x = 0; x <= cap[0]; ++x) {
    if (colHeight(p, x, 0) == 0) break;
    for (int y = 0; y <= cap[1]; ++y) {
      int h = colHeight(p, x, y);
      if (h == 0) break;
      for (int z = std::min(h - 1, cap[2]); z >= 0; --z) {
        if (x == 0 && y == 0 && z == 0) continue;
        u64 m = pack(x, y, z);
        child(p, m, c);
        Child ch;
        ch.m = m;
        keyOf(c, ch.a, ch.b);
        ch.score = unboundedAxes(c) * 1000 + c.n;
        out.push_back(ch);
      }
    }
  }
  std::stable_sort(out.begin(), out.end(), [](const Child& u, const Child& v) { return u.score < v.score; });
  return truncated;
}

// ---- rod oracle: positions with exactly one unbounded axis ----
static std::map<std::string, std::unique_ptr<rod::RodSolver>> rodSolvers;
static long long oracleCalls = 0, oracleExact = 0, oracleAborted = 0;
static long long ORACLE_BUDGET = 20000;  // -B: new rod evaluations allowed per oracle call
static std::unordered_map<u64, char> oracleFailed;  // positions whose oracle call was aborted

// Convert a position with one unbounded axis k into rod form: cross-section over the two other
// axes (u, v), heights along k. Returns false if out of the oracle's range.
static bool toRod(const Pos& p, std::string& cols, rod::H& h, int& nW) {
  int nb[3], e[3];
  bounds(p, nb, e);
  int k = -1, cnt = 0;
  for (int i = 0; i < 3; ++i) if (nb[i] == INFC) { k = i; ++cnt; }
  if (cnt != 1) return false;
  int u = (k == 0) ? 1 : 0, v = (k == 2) ? 1 : 2;
  if (nb[u] > 9 || nb[v] > 9) return false;
  auto coord = [](u64 g, int i) { return i == 0 ? fx(g) : i == 1 ? fy(g) : fz(g); };
  cols.clear();
  h.clear();
  nW = 0;
  for (int a = 0; a < nb[u]; ++a) {
    int count = 0;
    for (int b = 0; b < nb[v]; ++b) {
      int ht = INFC;
      for (int i = 0; i < p.n; ++i)
        if (coord(p.g[i], u) <= a && coord(p.g[i], v) <= b) ht = std::min(ht, coord(p.g[i], k));
      if (ht == 0) break;
      if (ht != INFC && ht > 250) return false;
      h.push_back(ht == INFC ? rod::OMEGA : (uint8_t)ht);
      if (ht == INFC && !(a == 0 && b == 0)) ++nW;
      ++count;
    }
    if (count == 0) break;
    cols.push_back('0' + count);
  }
  if (h.size() > 16) return false;
  return true;
}

// Returns true if the oracle decided the position (and stores the result in the TT).
static bool tryOracle(const Pos& p, u64 ka, u64 kb) {
  if (!ORACLE) return false;
  std::string cols;
  rod::H h;
  int nW;
  if (!toRod(p, cols, h, nW)) return false;
  if (!(nW <= ORACLE_W || (int)h.size() <= ORACLE_SMALL)) return false;
  if (oracleFailed.count(ka ^ (kb * 31))) return false;
  auto it = rodSolvers.find(cols);
  if (it == rodSolvers.end()) it = rodSolvers.emplace(cols, std::make_unique<rod::RodSolver>(cols)).first;
  rod::RodSolver& R = *it->second;
  R.budgetEnd = R.fcount + R.wcount + ORACLE_BUDGET;
  uint8_t r;
  try {
    r = R.decide(h);
  } catch (const rod::Abort&) {
    R.budgetEnd = -1;
    ++oracleAborted;
    oracleFailed.emplace(ka ^ (kb * 31), 1);
    return false;
  }
  R.budgetEnd = -1;
  ++oracleCalls;
  bool exact = r & 2;
  if (exact) ++oracleExact;
  if (r & 1) tt.put(ka, kb, INF, 0, exact ? 1 : 0);
  else tt.put(ka, kb, 0, INF, exact ? 1 : 0);
  return true;
}

static long long expansions = 0;
static std::chrono::steady_clock::time_point t0;
static bool timedOut = false;

static void lookupPD(u64 a, u64 b, u32& phi, u32& delta, bool& exact) {
  Entry* e = tt.find(a, b);
  if (e) { phi = e->phi; delta = e->delta; exact = e->flags & 1; }
  else { phi = 1; delta = 1; exact = false; }
}

static void mid(const Pos& p, u64 ka, u64 kb, u32 thphi, u32 thdelta) {
  if (timedOut) return;
  Entry* e = tt.find(ka, kb);
  if (e && (e->phi >= thphi || e->delta >= thdelta)) return;
  if (!e) {
    bool done = tryOracle(p, ka, kb);
    double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    if (s > TLIMIT) timedOut = true;
    if (done) return;
  }
  ++expansions;
  if ((expansions & 0x3FFF) == 0) {
    double s = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
    if (s > TLIMIT) { timedOut = true; return; }
  }
  std::vector<Child> ch;
  bool truncated = genChildren(p, ch);
  if (ch.empty()) { tt.put(ka, kb, INF, 0, 1); return; }  // only the poison: P, exact
  Pos c;
  while (true) {
    u32 phi = INF, delta = 0, d2 = INF;
    int best = -1;
    bool allExact = true;
    int provenP = -1;
    bool provenPExact = false;
    for (int i = 0; i < (int)ch.size(); ++i) {
      u32 cp, cd;
      bool ce;
      lookupPD(ch[i].a, ch[i].b, cp, cd, ce);
      if (cd == 0) {  // child proven P
        if (provenP < 0 || (ce && !provenPExact)) { provenP = i; provenPExact = ce; }
      }
      if (cd < phi) { d2 = phi; phi = cd; best = i; }
      else if (cd < d2) d2 = cd;
      delta = std::min<u32>(INF, delta + cp);
      if (!(cp == 0 && ce)) allExact = false;
    }
    if (provenP >= 0) { tt.put(ka, kb, 0, INF, provenPExact ? 1 : 0); return; }
    if (delta == 0) { tt.put(ka, kb, INF, 0, (!truncated && allExact) ? 1 : 0); return; }
    if (phi >= thphi || delta >= thdelta || timedOut) { tt.put(ka, kb, phi, delta, 0); return; }
    u32 cphi, cdelta;
    bool cex;
    lookupPD(ch[best].a, ch[best].b, cphi, cdelta, cex);
    u32 thphiC = (thdelta >= INF) ? INF : std::min<u64>(INF, (u64)thdelta - delta + cphi);
    u32 thdeltaC = std::min<u32>(thphi, d2 >= INF ? INF : d2 + 1);
    child(p, ch[best].m, c);
    mid(c, ch[best].a, ch[best].b, thphiC, thdeltaC);
    if (timedOut) { tt.put(ka, kb, phi, delta, 0); return; }
  }
}

// result: 1 = N, 0 = P, -1 = unknown; exact flag
static int solve(const Pos& p, bool& exact) {
  u64 a, b;
  keyOf(p, a, b);
  mid(p, a, b, INF, INF);
  Entry* e = tt.find(a, b);
  exact = e && (e->flags & 1);
  if (!e) return -1;
  if (e->phi == 0) return 1;
  if (e->delta == 0) return 0;
  return -1;
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

// Known exact P-positions (any orientation; canonicalised before insertion).
static void seed() {
  const char* known[] = {
      "0,1,0 0,0,2",  // 2 x omega (two infinite rows)
      "1,0,0 0,1,1",  // infinite L-shape (two infinite arms)
  };
  for (const char* s : known) {
    Pos p = parse(s);
    canon(p);
    u64 a, b;
    keyOf(p, a, b);
    tt.put(a, b, INF, 0, 1);
  }
}

static int g_argc;
static char** g_argv;
static const char* resStr(int r) { return r == 1 ? "N" : r == 0 ? "P" : "unknown"; }

static void* run(void*) {
  int i = 1;
  while (i + 1 < g_argc && g_argv[i][0] == '-') {
    if (!std::strcmp(g_argv[i], "-a")) ALPHA = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-d")) DSLACK = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-g")) GLOBALCAP = std::atoi(g_argv[i + 1]) != 0;
    else if (!std::strcmp(g_argv[i], "-t")) TLIMIT = std::atof(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-r")) ORACLE = std::atoi(g_argv[i + 1]) != 0;
    else if (!std::strcmp(g_argv[i], "-W")) ORACLE_W = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-B")) ORACLE_BUDGET = std::atoll(g_argv[i + 1]);
    else break;
    i += 2;
  }
  if (i + 1 >= g_argc) { std::fprintf(stderr, "usage: chomp3p [-a A] [-d D] [-g 0|1] [-t S] solve|why|moves \"x,y,z ...\"\n"); std::exit(1); }
  tt.init(1 << 22);
  seed();
  t0 = std::chrono::steady_clock::now();
  const char* mode = g_argv[i];
  Pos p = parse(g_argv[i + 1]);
  Pos pc = p;
  canon(pc);
  auto secs = [] { return std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count(); };
  if (!std::strcmp(mode, "solve") || !std::strcmp(mode, "why")) {
    bool ex;
    int r = solve(pc, ex);
    std::printf("%s : %s%s   [a=%d d=%d g=%d; %lld expansions, %zu TT entries, %lld rod-oracle calls (%lld exact, %lld aborted), %.1fs]\n",
                show(p).c_str(), resStr(r), r < 0 ? "" : (ex ? " exact" : " heuristic"), ALPHA, DSLACK, (int)GLOBALCAP,
                expansions, tt.used, oracleCalls, oracleExact, oracleAborted, secs());
    if (!std::strcmp(mode, "why") && r >= 0) {
      std::vector<Child> ch;
      genChildren(pc, ch);
      Pos c;
      for (auto& x : ch) {
        u32 cp, cd;
        bool ce;
        lookupPD(x.a, x.b, cp, cd, ce);
        if (r == 1 && cd == 0) {
          child(pc, x.m, c);
          std::printf("  move (%d,%d,%d) -> %s : P%s\n", fx(x.m), fy(x.m), fz(x.m), show(c).c_str(), ce ? "" : "?");
          break;
        }
        if (r == 0) {
          child(pc, x.m, c);
          std::printf("  option (%d,%d,%d) -> %s : N%s\n", fx(x.m), fy(x.m), fz(x.m), show(c).c_str(), ce ? "" : "?");
        }
      }
    }
  } else if (!std::strcmp(mode, "moves")) {
    std::vector<Child> ch;
    genChildren(pc, ch);
    std::printf("%s : winning moves (canonical orientation %s):", show(p).c_str(), show(pc).c_str());
    std::fflush(stdout);
    Pos c;
    int unknown = 0;
    for (auto& x : ch) {
      child(pc, x.m, c);
      bool ex;
      int r = solve(c, ex);
      if (r == 0) { std::printf(" (%d,%d,%d)%s", fx(x.m), fy(x.m), fz(x.m), ex ? "" : "?"); std::fflush(stdout); }
      if (r < 0) ++unknown;
      if (timedOut) break;
    }
    std::printf("   [%d unknown%s; %lld expansions, %.1fs]  (? = heuristic)\n", unknown, timedOut ? ", TIMED OUT" : "",
                expansions, secs());
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
