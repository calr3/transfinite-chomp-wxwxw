// Ordinal Grundy values of 2D Chomp positions with some infinite rows (Idea D).
//
// A position is k rows of lengths a[0] >= a[1] >= ... >= a[k-1], each in N or omega. Row 0
// holds the poison cell (0,0). Taking cell (x, r) cuts every row r' >= r to length min(a[r'], x).
// Values are ordinals below omega^2, encoded as n * BIG + m for omega*n + m.
//
// Finite positions: exact Grundy values by memoised recursion.
// One infinite row (exact): G(omega, R) = omega + gamma(R), where gamma is the normal-play
// Grundy value of the rows R with no poison. (The truncations (x, R) form a row of the mex table
// that blocks its own past and finitely many other injective sequences, so it takes every
// natural value; the remaining options are (omega, R') with values omega + gamma(R').)
// Two or more infinite rows: the cuts of an infinite row r at x = 0, 1, 2, ... form a family,
// computed for x up to F + T (F = largest finite length, T = -t). The mex is taken over the
// computed values, except that a gap at least FRONT times the largest value seen at that level
// is treated as an artefact of the range (the level is assumed covered). Such results are
// HEURISTIC; they are flagged, and should be checked for stability in T (notes/09-rows.md).
//
// Usage: rows [-t T] [-F FRONT] r0,r1,...  ('w' = omega), e.g. rows w,w,w  or  rows w,w,3
//        (-F 1e9 disables the frontier rule: the mex of the computed values, a lower bound)
//        rows [-t T] -table K MAXLEN   values of all positions with K rows, the first J
//                                       infinite (J = 0..K) and the rest <= MAXLEN
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <pthread.h>
#include <string>
#include <unordered_map>
#include <vector>

using i64 = int64_t;
static const int W = 255;
static const i64 BIG = 1LL << 24;
static int T = 24;
static bool TAILS = false;  // old contiguous-run tail inference (superseded)
// Frontier rule for levels where no exact argument is available: if the least missing value at
// a level is at least FRONT times the largest observed value there, the gap is probably an
// artefact of the computed range, and the level is assumed covered.
static double FRONT = 0.5;
static bool assumed = false;
static int K = 0;

using Rows = std::vector<int>;

static uint64_t key(const Rows& a) {
  uint64_t k = 0;
  for (int v : a) k = k * 256 + v;
  return k;
}

static std::unordered_map<uint64_t, i64> memo;
static bool overflow = false;

static std::string ord(i64 v) {
  long long n = v / BIG, m = v % BIG;
  std::string s;
  if (n == 1) s = "w";
  else if (n > 1) s = "w*" + std::to_string(n);
  if (m != 0 || n == 0) s += (n ? "+" : "") + std::to_string(m);
  return s;
}

static Rows cut(const Rows& a, int r, int x) {
  Rows b = a;
  for (int i = r; i < (int)b.size(); ++i) if (b[i] > x) b[i] = x;
  while (!b.empty() && b.back() == 0) b.pop_back();
  return b;
}

// A set of ordinals: explicit values plus, per level n, an optional tail [M, infinity).
struct VSet {
  std::vector<i64> vals;
  std::map<i64, i64> tail;  // level -> M
};

static i64 mex(const VSet& s, bool frontier) {
  std::map<i64, std::vector<i64>> byLevel;
  for (i64 v : s.vals) byLevel[v / BIG].push_back(v % BIG);
  for (i64 n = 0;; ++n) {
    std::vector<i64>& ms = byLevel[n];
    std::sort(ms.begin(), ms.end());
    ms.erase(std::unique(ms.begin(), ms.end()), ms.end());
    auto t = s.tail.find(n);
    i64 limit = (t == s.tail.end()) ? (i64)1 << 60 : t->second;
    i64 m = 0;
    for (i64 x : ms) { if (x == m) ++m; else if (x > m) break; }
    if (m < limit) {
      if (frontier && !ms.empty() && m >= 4 && m >= FRONT * ms.back()) { assumed = true; continue; }
      return n * BIG + m;
    }
    if (n > 50) { overflow = true; return n * BIG; }
  }
}

static i64 G(const Rows& a);

// Normal-play Grundy value of a finite Young diagram with NO poison (every cell may be taken;
// the player who cannot move loses). Rows given longest first.
static std::unordered_map<uint64_t, i64> gmemo;
static i64 gammaV(const Rows& a) {
  if (a.empty()) return 0;
  uint64_t k = key(a) ^ 0x8000000000000000ull;
  auto it = gmemo.find(k);
  if (it != gmemo.end()) return it->second;
  std::vector<i64> vs;
  for (int r = 0; r < (int)a.size(); ++r)
    for (int x = 0; x < a[r]; ++x) vs.push_back(gammaV(cut(a, r, x)));
  std::sort(vs.begin(), vs.end());
  i64 m = 0;
  for (i64 v : vs) { if (v == m) ++m; else if (v > m) break; }
  gmemo.emplace(k, m);
  return m;
}


// Values of the family of cuts of infinite row r, with a tail if the family ends in a long
// contiguous run at one level.
static void family(const Rows& a, int r, VSet& out) {
  int F = 0;
  for (int v : a) if (v != W) F = std::max(F, v);
  int x0 = (r == 0) ? 1 : 0, X = F + T;
  std::vector<i64> seq;
  for (int x = x0; x <= X; ++x) seq.push_back(G(cut(a, r, x)));
  for (i64 v : seq) out.vals.push_back(v);
  if (!TAILS) return;
  int L = seq.size();
  i64 lvl = seq.back() / BIG;
  for (int i = L - L / 3; i < L; ++i) if (seq[i] / BIG != lvl) return;  // no stable level
  std::vector<i64> ms;
  for (i64 v : seq) if (v / BIG == lvl) ms.push_back(v % BIG);
  std::sort(ms.begin(), ms.end());
  ms.erase(std::unique(ms.begin(), ms.end()), ms.end());
  i64 top = ms.back(), margin = L / 4;
  i64 hi = top - margin;
  // smallest M such that [M, hi] is contained in ms
  i64 M = hi;
  while (M - 1 >= 0 && std::binary_search(ms.begin(), ms.end(), M - 1)) --M;
  if (!std::binary_search(ms.begin(), ms.end(), hi)) return;
  if (hi - M < L / 3) return;  // run too short to trust
  auto it = out.tail.find(lvl);
  if (it == out.tail.end() || it->second > M) out.tail[lvl] = M;
}

static i64 G(const Rows& a) {
  if (a.empty()) return 0;  // cannot happen for valid positions (poison row exists)
  uint64_t k = key(a);
  auto it = memo.find(k);
  if (it != memo.end()) return it->second;
  int nw = 0;
  for (int v : a) if (v == W) ++nw;
  if (nw == 1) {  // exact: G(omega, R) = omega + gamma(R)
    Rows R(a.begin() + 1, a.end());
    i64 v = BIG + gammaV(R);
    memo.emplace(k, v);
    return v;
  }
  VSet s;
  for (int r = 0; r < (int)a.size(); ++r) {
    if (a[r] == W) {
      family(a, r, s);
    } else {
      for (int x = (r == 0 ? 1 : 0); x < a[r]; ++x) s.vals.push_back(G(cut(a, r, x)));
    }
  }
  i64 v = mex(s, nw >= 3);  // two infinite rows: values are finite, the rule misfires there
  memo.emplace(k, v);
  return v;
}

static Rows parse(const char* s) {
  Rows a;
  std::string str(s);
  size_t i = 0;
  while (i < str.size()) {
    size_t j = str.find(',', i);
    if (j == std::string::npos) j = str.size();
    std::string tok = str.substr(i, j - i);
    a.push_back(tok == "w" ? W : std::atoi(tok.c_str()));
    i = j + 1;
  }
  return a;
}

static std::string show(const Rows& a) {
  std::string s = "(";
  for (size_t i = 0; i < a.size(); ++i) {
    if (i) s += ",";
    s += a[i] == W ? "w" : std::to_string(a[i]);
  }
  return s + ")";
}

static int g_argc;
static char** g_argv;
static void* run(void*) {
  int i = 1;
  while (i + 1 < g_argc && (!std::strcmp(g_argv[i], "-t") || !std::strcmp(g_argv[i], "-F"))) {
    if (!std::strcmp(g_argv[i], "-t")) T = std::atoi(g_argv[i + 1]);
    else FRONT = std::atof(g_argv[i + 1]);  // -F 1e9 disables the frontier rule
    i += 2;
  }
  if (i < g_argc && !std::strcmp(g_argv[i], "-table")) {
    int k = std::atoi(g_argv[i + 1]), maxlen = std::atoi(g_argv[i + 2]);
    for (int j = 1; j <= k; ++j) {
      // rows: j infinite, then k - j finite rows (non-increasing, <= maxlen, >= 0)
      std::vector<Rows> list;
      std::vector<int> cur;
      auto gen = [&](auto&& self, int idx, int maxv) -> void {
        if (idx == k - j) {
          Rows a(j, W);
          for (int v : cur) a.push_back(v);
          while (!a.empty() && a.back() == 0) a.pop_back();
          list.push_back(a);
          return;
        }
        for (int v = 0; v <= maxv; ++v) { cur.push_back(v); self(self, idx + 1, v); cur.pop_back(); }
      };
      gen(gen, 0, maxlen);
      for (auto& a : list) std::printf("%-20s %s\n", show(a).c_str(), ord(G(a)).c_str());
    }
  } else {
    for (; i < g_argc; ++i) {
      Rows a = parse(g_argv[i]);
      i64 v = G(a);
      std::printf("%s : %s%s%s   [T=%d, %zu positions]\n", show(a).c_str(), ord(v).c_str(), overflow ? " (overflow)" : "",
                  assumed ? " (frontier rule used)" : "", T, memo.size());
      assumed = false;
    }
  }
  return nullptr;
}

int main(int argc, char** argv) {
  g_argc = argc;
  g_argv = argv;
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)2 << 30);
  pthread_t th;
  pthread_create(&th, &attr, run, nullptr);
  pthread_join(th, nullptr);
  return 0;
}
