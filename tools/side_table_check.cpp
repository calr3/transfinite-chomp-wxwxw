// Numerical check of the hypotheses of lean/Chomp/SideClass.lean (structure `Table`).
//
// The Lean file proves the side-class theorem for any function f : N -> N -> N satisfying eleven
// statements taken from Brouwer et al. and Sheiner. This program computes the actual function
// f(q,r) of three-row Chomp (as in side3row.cpp) and checks each statement, exactly as written
// in Lean, for all arguments up to N. It guards against a mis-stated hypothesis.
//   f(q,r) = A(q,r) while row r has not become constant, and tau(r) afterwards.
// usage: side_table_check N        (memory about 4 N^2 bytes)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int N;
static std::vector<int32_t> A;
static std::vector<int> tau;
static inline int32_t& a0(int b, int c) { return A[(size_t)b * (N + 1) + c]; }
static inline int f(int q, int r) { int v = a0(q, r); return v >= 0 ? v : tau[r]; }

int main(int argc, char** argv) {
  if (argc < 2) { std::fprintf(stderr, "usage: side_table_check N\n"); return 1; }
  N = std::atoi(argv[1]);
  const int K = N + 64;
  const long long V = (long long)N + K + 128, VW = V / 64 + 2, RW = K / 64 + 3;
  A.assign((size_t)(N + 1) * (N + 1), -1); tau.assign(N + 1, -1);
  {
    std::vector<uint64_t> row((size_t)(N + 1) * RW, 0), diag(VW, 0), col(VW, 0);
    for (int c = 0; c <= N; ++c) {
      if (c >= 1) { long long d = a0(c - 1, c - 1); diag[d >> 6] |= 1ull << (d & 63); }
      std::fill(col.begin(), col.end(), 0);
      for (int b = c; b <= N; ++b) {
        long long w0 = b >> 6, w = w0, a = -1;
        uint64_t mask = (1ull << (b & 63)) - 1; if (b == 0) mask = 1;
        const uint64_t* rw = &row[(size_t)b * RW];
        for (;;) {
          if (w - w0 >= RW) { std::fprintf(stderr, "offset overflow\n"); return 1; }
          uint64_t x = rw[w - w0] | col[w] | diag[w] | mask;
          if (x != ~0ull) { a = w * 64 + __builtin_ctzll(~x); break; }
          mask = 0; ++w;
        }
        a0(b, c) = (int32_t)a;
        row[(size_t)b * RW + ((a >> 6) - w0)] |= 1ull << (a & 63);
        col[a >> 6] |= 1ull << (a & 63);
        if (a == b && b > c) { tau[c] = b; break; }
      }
    }
  }
  const int VM = 2 * N + 400;
  long bad[11] = {0}; long cnt[11] = {0};
  // gt_row, enc, diag_max
  for (int q = 0; q <= N; ++q) for (int r = 0; r <= q; ++r) {
    int v = f(q, r);
    ++cnt[0]; if (!(r < v)) ++bad[0];
    if (v < q) { ++cnt[1]; if (f(v, r) != v) ++bad[1]; }
    ++cnt[9]; if (v > f(q, q)) ++bad[9];
  }
  // const
  for (int r = 0; r <= N; ++r) for (int k = r + 1; k <= N; ++k) if (f(k, r) == k)
    for (int q = k; q <= N; ++q) { ++cnt[2]; if (f(q, r) != k) ++bad[2]; }
  // row_inj
  { std::vector<int> seen(VM, -1);
    for (int q = 0; q <= N; ++q) for (int b = 0; b <= q; ++b) { int v = f(q, b); ++cnt[3]; if (seen[v] == q) ++bad[3]; seen[v] = q; } }
  // col_once: s < t1 < t2 < p, f t1 s = p  =>  f t2 s != p
  { std::vector<int> first(VM, -1), stamp(VM, -1);
    for (int s = 0; s <= N; ++s) for (int t = s + 1; t <= N; ++t) { int p = f(t, s);
      if (stamp[p] == s && first[p] < t && t < p) { ++bad[4]; }
      if (stamp[p] != s) { stamp[p] = s; first[p] = t; }
      ++cnt[4]; } }
  // row_start
  for (int r = 0; r <= N; ++r) { int p = tau[r]; if (p < 0) continue;
    for (int q = r + 1; q < p; ++q) { ++cnt[5]; bool ok = false; for (int b = 0; b < r && !ok; ++b) ok = f(q, b) == p; if (!ok) ++bad[5]; } }
  // diag_ne_partner, cover, diag_inj
  { std::vector<char> isP(VM, 0), isD(VM, 0);
    for (int r = 0; r <= N; ++r) if (tau[r] >= 0) isP[tau[r]] = 1;
    for (int a = 0; a <= N; ++a) { int d = f(a, a); ++cnt[10]; if (isD[d]) ++bad[10]; isD[d] = 1; }
    for (int h = 1; h <= N; ++h) { ++cnt[6]; if (isP[h] && isD[h]) ++bad[6]; }
    // cover: partners of rows < h and diagonal values of rows < h are all computed for h <= N/2
    for (int h = 1; h <= N / 2; ++h) { ++cnt[7]; if (!isP[h] && !isD[h]) ++bad[7]; } }
  // diag_mex
  { std::vector<int> seen(VM, -1); std::vector<char> isDlow(VM, 0);
    for (int a = 0; a <= N; ++a) {
      for (int b = 0; b < a; ++b) seen[f(a, b)] = a;
      int d = f(a, a);
      for (int v = 1; v < d; ++v) { ++cnt[8]; if (!isDlow[v] && seen[v] != a) ++bad[8]; }
      isDlow[d] = 1; } }
  const char* name[11] = {"gt_row", "enc", "const", "row_inj", "col_once", "row_start", "diag_ne_partner", "cover", "diag_mex", "diag_max", "diag_inj"};
  long tot = 0;
  for (int i = 0; i < 11; ++i) { std::printf("%-16s %12ld instances, %ld violations\n", name[i], cnt[i], bad[i]); tot += bad[i]; }
  std::printf("N = %d: %s\n", N, tot ? "VIOLATIONS FOUND" : "all eleven hypotheses hold");
  return tot ? 1 : 0;
}
