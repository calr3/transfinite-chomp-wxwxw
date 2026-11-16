// General solver for 3D Chomp positions on N^3, including positions with infinite parts.
//
// A position is a downset X = N^3 \ up(G), stored as the finite antichain G of minimal
// eaten cells ("generators"). The full board N^3 has G = {}; a finite base B x omega has
// generators that bound x and y; omega x omega x c has G = {(0,0,c)}.
//
// Moves: any cell m in X except the poison (0,0,0). The child is N^3 \ up(G + m).
//
// Positions with an infinite part have infinitely many moves. We consider only moves whose
// coordinate on each axis is at most cap_i = ALPHA * E_i + D, where E_i is the largest i-th
// coordinate of any generator (0 if none). The cap is relative to the position, so after a
// move establishes finite heights, the remaining infinite parts can still be cut above them
// (with a fixed cap the game would collapse to a finite box, where strategy stealing makes
// every box an N-position, including 2 x omega, which is really P).
//
// Exactness. A result is EXACT when it does not depend on the cap:
//   * N is exact if it is witnessed by an exact P child;
//   * P is exact if the cap did not cut off any move (the position is finite and within the
//     caps) and every child is exactly N.
// Every other result is HEURISTIC: it assumes no winning move exists beyond the caps.
// Re-running with larger ALPHA and D and getting the same answer is evidence, not proof.
//
// Positions are canonicalised under the 6 coordinate permutations (Chomp on N^3 is
// symmetric under them, and so are the caps).
//
// Usage:
//   chomp3 [-a ALPHA] [-d D] solve "x,y,z x,y,z ..."   decide one position
//   chomp3 [-a ALPHA] [-d D] moves "x,y,z ..."         list winning moves (within the caps)
//   chomp3 [-a ALPHA] [-d D] why "x,y,z ..." [DEPTH]    winning move of an N-position, or
//                                                       every option of a P-position, recursively
// An empty generator string "" is the full board N^3.
#include <algorithm>
#include <array>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <string>
#include <unordered_map>
#include <vector>

using u64 = uint64_t;
using P3 = std::array<int, 3>;
using Gens = std::vector<P3>;

static int ALPHA = 2, DSLACK = 6;
static const int INF = 1 << 29;

struct Key {
  u64 a, b;
  bool operator==(const Key& o) const { return a == o.a && b == o.b; }
};
struct KeyHash {
  size_t operator()(const Key& k) const { return k.a ^ (k.b * 0x9E3779B97F4A7C15ull); }
};
// value bits: 1 = N (win), 2 = exact
static std::unordered_map<Key, uint8_t, KeyHash> memo;

static u64 mix(u64 x) {
  x += 0x9E3779B97F4A7C15ull;
  x = (x ^ (x >> 30)) * 0xBF58476D1CE4E5B9ull;
  x = (x ^ (x >> 27)) * 0x94D049BB133111EBull;
  return x ^ (x >> 31);
}

static bool leq(const P3& a, const P3& b) { return a[0] <= b[0] && a[1] <= b[1] && a[2] <= b[2]; }

static const int PERMS[6][3] = {{0, 1, 2}, {0, 2, 1}, {1, 0, 2}, {1, 2, 0}, {2, 0, 1}, {2, 1, 0}};

// Canonical form: lexicographically least sorted generator list over the 6 permutations.
static Gens canon(const Gens& g) {
  Gens best;
  bool first = true;
  for (auto& p : PERMS) {
    Gens h;
    h.reserve(g.size());
    for (auto& q : g) h.push_back({q[p[0]], q[p[1]], q[p[2]]});
    std::sort(h.begin(), h.end());
    if (first || h < best) { best = h; first = false; }
  }
  return best;
}

static Key keyOf(const Gens& g) {
  u64 a = 0x1234567ull + g.size(), b = 0x89abcdefull ^ g.size();
  for (auto& q : g) {
    u64 v = ((u64)q[0] << 40) ^ ((u64)q[1] << 20) ^ (u64)q[2];
    a = mix(a ^ v);
    b = mix(b + v * 0x2545F4914F6CDD1Dull);
  }
  return {a, b};
}

static Gens child(const Gens& g, const P3& m) {
  Gens h;
  h.reserve(g.size() + 1);
  for (auto& q : g)
    if (!leq(m, q)) h.push_back(q);
  h.push_back(m);
  return canon(h);
}

// Natural bound on each axis (INF if the position is unbounded in that direction).
static void bounds(const Gens& g, int nb[3]) {
  for (int i = 0; i < 3; ++i) {
    nb[i] = INF;
    for (auto& q : g) {
      bool axis = true;
      for (int j = 0; j < 3; ++j)
        if (j != i && q[j] != 0) axis = false;
      if (axis) nb[i] = std::min(nb[i], q[i]);
    }
  }
}

static void caps(const Gens& g, int cap[3], bool& truncated) {
  int nb[3];
  bounds(g, nb);
  truncated = false;
  for (int i = 0; i < 3; ++i) {
    int e = 0;
    for (auto& q : g) e = std::max(e, q[i]);
    int c = ALPHA * e + DSLACK;
    if (nb[i] - 1 <= c) c = nb[i] - 1;  // the whole axis range is covered
    else truncated = true;
    cap[i] = c;
  }
}

// Height of column (x, y): the least z with (x,y,z) eaten.
static int colHeight(const Gens& g, int x, int y) {
  int h = INF;
  for (auto& q : g)
    if (q[0] <= x && q[1] <= y) h = std::min(h, q[2]);
  return h;
}

static long long nodes = 0;

// returns bits: 1 = N, 2 = exact
static uint8_t solve(const Gens& g) {
  Key k = keyOf(g);
  auto it = memo.find(k);
  if (it != memo.end()) return it->second;
  ++nodes;
  int cap[3];
  bool truncated;
  caps(g, cap, truncated);
  bool win = false, winExact = false, allExact = true;
  for (int x = 0; x <= cap[0] && !winExact; ++x) {
    if (colHeight(g, x, 0) == 0) break;
    for (int y = 0; y <= cap[1] && !winExact; ++y) {
      int h = colHeight(g, x, y);
      if (h == 0) break;
      int zmax = std::min(h - 1, cap[2]);
      for (int z = zmax; z >= 0 && !winExact; --z) {
        if (x == 0 && y == 0 && z == 0) continue;
        uint8_t r = solve(child(g, {x, y, z}));
        bool cN = r & 1, cE = r & 2;
        if (!cN) {
          win = true;
          if (cE) winExact = true;
          else break;  // heuristic witness found: stop (no search for an exact one)
        } else if (!cE) {
          allExact = false;
        }
      }
      if (win && !winExact) break;
    }
    if (win && !winExact) break;
  }
  uint8_t res;
  if (win) res = 1 | (winExact ? 2 : 0);
  else res = (!truncated && allExact) ? 2 : 0;
  memo.emplace(k, res);
  return res;
}

static Gens parse(const char* s) {
  Gens g;
  std::string str(s);
  size_t i = 0;
  while (i < str.size()) {
    while (i < str.size() && (str[i] == ' ' || str[i] == ';')) ++i;
    if (i >= str.size()) break;
    int a, b, c, n;
    if (std::sscanf(str.c_str() + i, "%d,%d,%d%n", &a, &b, &c, &n) != 3) {
      std::fprintf(stderr, "bad generator list\n");
      std::exit(1);
    }
    g.push_back({a, b, c});
    i += n;
  }
  // reduce to the minimal antichain
  Gens h;
  for (auto& q : g) {
    bool dominated = false;
    for (auto& r : g)
      if (&r != &q && leq(r, q) && r != q) dominated = true;
    if (!dominated && std::find(h.begin(), h.end(), q) == h.end()) h.push_back(q);
  }
  return h;
}

static std::string show(const Gens& g) {
  std::string s;
  for (auto& q : g) {
    char buf[64];
    std::snprintf(buf, sizeof buf, "%s(%d,%d,%d)", s.empty() ? "" : " ", q[0], q[1], q[2]);
    s += buf;
  }
  return s.empty() ? "{}" : s;
}

// Print why a position is N (one winning move) or P (each option's winning reply).
static void explain(const Gens& g, int indent, int depth) {
  uint8_t r = solve(g);
  std::printf("%*s%s : %s%s\n", indent, "", show(g).c_str(), (r & 1) ? "N" : "P", (r & 2) ? "" : "?");
  if (depth <= 0) return;
  int cap[3];
  bool truncated;
  caps(g, cap, truncated);
  for (int x = 0; x <= cap[0]; ++x)
    for (int y = 0; y <= cap[1]; ++y) {
      int h = colHeight(g, x, y);
      for (int z = std::min(h, cap[2] + 1) - 1; z >= 0; --z) {
        if (x == 0 && y == 0 && z == 0) continue;
        Gens c = child(g, {x, y, z});
        uint8_t rc = solve(c);
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
  while (i < g_argc && g_argv[i][0] == '-' && g_argv[i][1] != 0 && i + 1 < g_argc) {
    if (!std::strcmp(g_argv[i], "-a")) ALPHA = std::atoi(g_argv[i + 1]);
    else if (!std::strcmp(g_argv[i], "-d")) DSLACK = std::atoi(g_argv[i + 1]);
    else break;
    i += 2;
  }
  if (i + 1 >= g_argc) {
    std::fprintf(stderr, "usage: chomp3 [-a ALPHA] [-d D] solve|moves \"x,y,z ...\"\n");
    std::exit(1);
  }
  const char* mode = g_argv[i];
  Gens g = parse(g_argv[i + 1]);
  if (!std::strcmp(mode, "solve")) {
    uint8_t r = solve(canon(g));
    std::printf("%s : %s %s   [alpha=%d d=%d, %lld positions]\n", show(g).c_str(),
                (r & 1) ? "N" : "P", (r & 2) ? "exact" : "heuristic", ALPHA, DSLACK, nodes);
  } else if (!std::strcmp(mode, "moves")) {
    int cap[3];
    bool truncated;
    caps(g, cap, truncated);
    std::printf("%s : winning moves (caps %d,%d,%d):", show(g).c_str(), cap[0], cap[1], cap[2]);
    for (int x = 0; x <= cap[0]; ++x)
      for (int y = 0; y <= cap[1]; ++y) {
        int h = colHeight(g, x, y);
        for (int z = 0; z < std::min(h, cap[2] + 1); ++z) {
          if (x == 0 && y == 0 && z == 0) continue;
          uint8_t r = solve(child(g, {x, y, z}));
          if (!(r & 1)) std::printf(" (%d,%d,%d)%s", x, y, z, (r & 2) ? "" : "?");
        }
      }
    std::printf("   [alpha=%d d=%d, %lld positions]  (? = heuristic)\n", ALPHA, DSLACK, nodes);
  } else if (!std::strcmp(mode, "why")) {
    // Follow winning moves: print the position, a winning move and the child, recursively
    // through P children (all of whose options are N), down to the given depth.
    int depth = (i + 2 < g_argc) ? std::atoi(g_argv[i + 2]) : 1;
    explain(canon(g), 0, depth);
  } else {
    std::fprintf(stderr, "unknown mode %s\n", mode);
    std::exit(1);
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
