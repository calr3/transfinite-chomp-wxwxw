// Checks for notes/19 (remaining lifetimes). Two families of 3-row Chomp are tabulated together,
// as in side3row_cube.cpp:
//   family 0: P-positions [a,b,c] (2D);  family 1: P-positions [a,b,c | cube], i.e. Grundy value 1.
// A(b,c) is the first row of the P-position with rows b >= c below it, or -1 once row c has become
// constant (tau(c) < b). "Time" is the level b: row c is born at time c and dies at time tau(c).
// Row c is alive at time t if c < t and (c is a side element or tau(c) > t).
//   n(t) = number of rows alive at t,  I(t) = #{c : tau(c) <= t},  s(v) = #(side elements <= v).
//
// Family 0 (all proved in notes/19; the program reports the number of violations, which must be 0):
//   L1  remaining lifetime: c alive at t, not side  =>  tau(c) - t <= #{b < c alive at t}
//   T3  I(T) <= 2 s(T-1);  also reported: the range of s(T-1) - I(T) (observed to be {0,1,2})
//   L4  A(a,a) >= a + n(a) + 1;  n(t) <= (2t+1)/3;  tau(r) <= r + n(r+1);  A(a,a) > tau(r) for a >= r
//   P6  side row r, V >= 2r+1:  #{q < V : A(q,r) > V} = #(non-side rows below r)
//   P7  #{q in (r,tau(r)) : A(q,r) < tau(r)} = #{b > r : tau(b) < tau(r)}  (both observed to be 0)
// Family 1 (cube): levels q in (r,p), p = tau1(r), are good (some b < r has A1(q,b) = p), cube
// (A0(q,r) = p) or dead. Reported:
//   remaining lifetime with dead levels: p - t <= #{b < r alive at t} + 1 + #(dead levels >= t)
//   every dead level has a row s < r with A0(q,s) = p that is alive in both families
//   inversions of tau1, coincidences (partner and diagonal value), levels whose diagonal value is
//   not the largest value of the level;
//   the hypotheses (H4) and (L) of the reduction in notes/19, section 9, and the low levels.
// usage: side_lifetime N      (rows up to N/2 are used; memory about 8 N^2 bytes)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

static int N;
static std::vector<int32_t> A0, A1;
static std::vector<int> tau0, tau1;
static inline int32_t& a0(int b, int c) { return A0[(size_t)b * (N + 1) + c]; }
static inline int32_t& a1(int b, int c) { return A1[(size_t)b * (N + 1) + c]; }

static bool build() {
  const int K = N + 64;
  const long long V = (long long)N + K + 128, VW = V / 64 + 2, RW = K / 64 + 3;
  A0.assign((size_t)(N + 1) * (N + 1), -1); A1.assign((size_t)(N + 1) * (N + 1), -1);
  std::vector<uint64_t> row0((size_t)(N + 1) * RW, 0), row1((size_t)(N + 1) * RW, 0);
  std::vector<uint64_t> diag0(VW, 0), diag1(VW, 0), col0(VW, 0), col1(VW, 0);
  tau0.assign(N + 1, -1); tau1.assign(N + 1, -1);
  auto setbit = [](uint64_t* w, long long i) { w[i >> 6] |= 1ull << (i & 63); };
  for (int c = 0; c <= N; ++c) {
    if (c >= 1) {
      if (a0(c - 1, c - 1) >= 0) setbit(diag0.data(), a0(c - 1, c - 1));
      if (a1(c - 1, c - 1) >= 0) setbit(diag1.data(), a1(c - 1, c - 1));
    }
    std::fill(col0.begin(), col0.end(), 0); std::fill(col1.begin(), col1.end(), 0);
    bool done0 = false, done1 = false;
    for (int b = c; b <= N && !(done0 && done1); ++b) {
      long long w0 = b >> 6;
      for (int fam = 0; fam < 2; ++fam) {
        if (fam == 0 ? done0 : done1) continue;
        const uint64_t* row = &(fam ? row1 : row0)[(size_t)b * RW];
        const uint64_t* col = (fam ? col1 : col0).data();
        const uint64_t* dg = (fam ? diag1 : diag0).data();
        int extra = fam ? a0(b, c) : -1;     // removing the cube leaves the 2D position
        long long w = w0, a = -1;
        uint64_t mask = (1ull << (b & 63)) - 1;
        if (b == 0) mask = 1;
        for (;;) {
          if (w - w0 >= RW) { std::fprintf(stderr, "offset overflow\n"); return false; }
          uint64_t x = row[w - w0] | col[w] | dg[w] | mask;
          if (extra >= 0 && (extra >> 6) == w) x |= 1ull << (extra & 63);
          if (x != ~0ull) { a = w * 64 + __builtin_ctzll(~x); break; }
          mask = 0; ++w;
        }
        (fam ? A1 : A0)[(size_t)b * (N + 1) + c] = (int32_t)a;
        uint64_t* rw = &(fam ? row1 : row0)[(size_t)b * RW];
        rw[(a >> 6) - w0] |= 1ull << (a & 63);
        setbit((fam ? col1 : col0).data(), a);
        if (a == b && b > c) { (fam ? tau1 : tau0)[c] = b; if (fam) done1 = true; else done0 = true; }
        if (a == b && b == c && b > 0 && fam == 1) { std::fprintf(stderr, "[%d,%d,%d | cube] is P\n", b, b, b); return false; }
      }
    }
  }
  return true;
}

int main(int argc, char** argv) {
  if (argc < 2) { std::fprintf(stderr, "usage: side_lifetime N\n"); return 1; }
  N = std::atoi(argv[1]); if (!build()) return 1;
  const int H = N / 2 - 2;                       // rows below H have tau decided
  auto alive = [](const std::vector<int>& tau, int b, int t) { return b < t && (tau[b] < 0 || tau[b] > t); };

  // ---------- family 0 ----------
  std::vector<int> s0(H + 2, 0), I0(H + 2, 0), n0(H + 2, 0);
  { int c = 0; for (int x = 0; x <= H; ++x) { if (tau0[x] < 0) ++c; s0[x] = c; } }
  { std::vector<int> cnt(H + 2, 0); for (int x = 0; x <= H; ++x) if (tau0[x] >= 0 && tau0[x] <= H) ++cnt[tau0[x]];
    int c = 0; for (int v = 0; v <= H; ++v) { c += cnt[v]; I0[v] = c; n0[v] = v - c; } }
  { long chk = 0, bad = 0; int slack = 1 << 30;
    for (int t = 1; t <= H; ++t) { int older = 0;
      for (int d = 0; d < t; ++d) { if (!alive(tau0, d, t)) continue;
        if (tau0[d] >= 0) { ++chk; int sl = older - (tau0[d] - t); if (sl < 0) ++bad; slack = std::min(slack, sl); }
        ++older; } }
    std::printf("fam0 L1 remaining lifetime: %ld pairs (t,row), violations %ld, least slack %d\n", chk, bad, slack); }
  { long bad = 0; int lo = 1 << 30, hi = -(1 << 30);
    for (int t = 1; t <= H; ++t) { int d = s0[t - 1] - I0[t]; if (2 * s0[t - 1] < I0[t]) ++bad; lo = std::min(lo, d); hi = std::max(hi, d); }
    std::printf("fam0 T3 I(T) <= 2 s(T-1), T <= %d: violations %ld; s(T-1) - I(T) ranges over [%d,%d]\n", H, bad, lo, hi); }
  { long b1 = 0, b2 = 0, b3 = 0, b4 = 0;
    for (int a = 1; a <= H; ++a) { if (a0(a, a) < a + n0[a] + 1) ++b1; if (3 * n0[a] > 2 * a + 1) ++b2; }
    for (int r = 0; r < H; ++r) { if (tau0[r] < 0 || tau0[r] > H) continue; if (tau0[r] > r + n0[r + 1]) ++b3; for (int a = r; a < tau0[r]; ++a) if (a0(a, a) <= tau0[r]) ++b4; }
    std::printf("fam0 L4 violations: A(a,a) >= a+n(a)+1: %ld; n(t) <= (2t+1)/3: %ld; tau(r) <= r+n(r+1): %ld; A(a,a) > tau(r) for a >= r: %ld\n", b1, b2, b3, b4); }
  { long rows = 0, chk = 0, bad = 0;
    for (int r = 1; r <= N / 8; ++r) { if (tau0[r] >= 0) continue; ++rows; int want = r - s0[r - 1];
      std::vector<int> ev(N + 2, 0); for (int q = r; q <= N / 2; ++q) { int v = a0(q, r); if (v <= N) ++ev[v]; }
      int le = 0; for (int V = r + 1; V <= N / 2 - 2 * r - 4; ++V) { le += ev[V]; if (V >= 2 * r + 1) { ++chk; if ((V - r) - le != want) ++bad; } } }
    std::printf("fam0 P6 excess identity: %ld side rows, %ld pairs (r,V), violations %ld\n", rows, chk, bad); }
  { long low = 0, inv = 0;
    for (int r = 0; r < H; ++r) { int p = tau0[r]; if (p < 0 || p > H) continue;
      for (int q = r + 1; q < p; ++q) if (a0(q, r) < p) ++low;
      for (int b = r + 1; b < p; ++b) if (tau0[b] >= 0 && tau0[b] < p) ++inv; }
    std::printf("fam0 P7: values below the partner %ld, inversions of tau %ld\n", low, inv); }

  // ---------- family 1 ----------
  { long parts = 0, lev = 0, good = 0, cube = 0, dead = 0, badLife = 0, noSrc = 0, srcNotBoth = 0; int maxDead = 0;
    for (int r = 1; r < H / 2; ++r) { int p = tau1[r]; if (p < 0) continue; ++parts;
      std::vector<char> g(p - r, 0);
      for (int q = r + 1; q < p; ++q) for (int b = 0; b < r; ++b) if (a1(q, b) == p) { g[q - r] = 1; break; }
      int deadAbove = 0;
      for (int t = p - 1; t > r; --t) { ++lev;
        if (g[t - r]) ++good; else if (a0(t, r) == p) ++cube; else {
          ++dead; ++deadAbove;
          int src = -1; for (int s2 = 0; s2 < r; ++s2) if (a0(t, s2) == p) src = s2;
          if (src < 0) ++noSrc; else if (!alive(tau1, src, t)) ++srcNotBoth; }
        int older = 0; for (int b = 0; b < r; ++b) if (alive(tau1, b, t)) ++older;
        if (p - t > older + 1 + deadAbove) ++badLife; }
      maxDead = std::max(maxDead, deadAbove); }
    std::printf("fam1, rows < %d: %ld partners; levels %ld = good %ld + cube %ld + dead %ld; most dead levels of one partner %d\n", H / 2, parts, lev, good, cube, dead, maxDead);
    std::printf("fam1 remaining lifetime with dead levels: violations %ld; dead levels without a 2D P-position [p,q,s], s < r: %ld; with s not alive in family 1: %ld\n", badLife, noSrc, srcNotBoth); }
  { long inv = 0, rowsInv = 0, own = 0, viaTau0 = 0; int far = 0, drop = 0, most = 0;
    for (int r = 0; r <= H; ++r) { int p = tau1[r]; if (p < 0) continue; int cnt = 0;
      for (int b = r + 1; b < p && b <= N; ++b) if (tau1[b] >= 0 && tau1[b] < p) { ++cnt; far = std::max(far, b - r); drop = std::max(drop, p - tau1[b]); if (tau1[b] == tau0[r]) ++viaTau0; }
      for (int q = r + 1; q < p; ++q) if (a1(q, r) < p) ++own;
      inv += cnt; if (cnt) ++rowsInv; most = std::max(most, cnt); }
    std::printf("fam1 inversions of tau1 (b > r, tau1(b) < tau1(r)), rows <= %d: %ld pairs in %ld rows, at most %d per row, b - r <= %d, tau1(r) - tau1(b) <= %d\n", H, inv, rowsInv, most, far, drop);
    std::printf("fam1: levels q in (r,p) with A1(q,r) < p: %ld; inversions with tau1(b) = tau0(r): %ld\n", own, viaTau0); }
  { std::vector<int> part(3 * N, -1); for (int z = 0; z <= N; ++z) if (tau1[z] >= 0) part[tau1[z]] = z;
    long coinc = 0, notmax = 0; int excess = 0, back = 0;
    for (int a = 1; a <= H; ++a) { int d = a1(a, a); if (part[d] >= 0) ++coinc; int mx = -1, mr = -1;
      for (int b = 0; b < a; ++b) { int v = a1(a, b); if (v > mx) { mx = v; mr = b; } }
      if (mx > d) { ++notmax; excess = std::max(excess, mx - d); back = std::max(back, a - mr); } }
    std::printf("fam1, levels <= %d: partner values that are diagonal values %ld; levels whose diagonal value is not the largest: %ld (by at most %d, the largest at most %d rows below)\n", H, coinc, notmax, excess, back); }
  { // high and low levels (notes/19, section 9)
    std::vector<int> part(3 * N, -1), dg(3 * N, -1), I1(H + 2, 0);
    for (int z = 0; z <= N; ++z) if (tau1[z] >= 0) part[tau1[z]] = z;
    for (int a = 0; a <= N; ++a) { int d = a1(a, a); if (d >= 0 && d < 3 * N) dg[d] = a; }
    { std::vector<int> c(H + 2, 0); for (int x = 0; x <= H; ++x) if (tau1[x] >= 0 && tau1[x] <= H) ++c[tau1[x]]; int t = 0; for (int v = 0; v <= H; ++v) { t += c[v]; I1[v] = t; } }
    long h4 = 0, olderAll = 0, olderDoomed = 0, low = 0, lowYoung = 0, lowDiag = 0, lowOld = 0, badL10 = 0, badDiag = 0; int mostLow = 0;
    for (int a = 0; a <= H; ++a) if (a1(a, a) > 2 * a + 2) ++badDiag;
    for (int r = 1; r <= H; ++r) { int p = tau1[r];
      for (int q = r + 1; q <= N; ++q) { int k = a1(q, r); if (k < 0) break; int b = k < 3 * N ? part[k] : -1; if (b >= 0 && b < r) { ++olderAll; if (p >= 0) ++olderDoomed; } }
      if (p < 0) continue;
      for (int a = r; a < p; ++a) if (a1(a, a) <= p) ++h4;
      int lw = 0;
      for (int q = r + 1; q < p; ++q) { int k = a1(q, r); if (k > p) continue; ++lw; int b = part[k]; if (b > r) ++lowYoung; else if (b >= 0) ++lowOld; else if (dg[k] >= r) ++lowDiag; }
      low += lw; mostLow = std::max(mostLow, lw);
      if (a1(r, r) > p && lw > r - I1[r]) ++badL10; }
    std::printf("fam1 (H4) tau1(r) < A1(a,a) for a >= r: violations %ld; A1(a,a) <= 2a+2: violations %ld\n", h4, badDiag);
    std::printf("fam1 (L) picks of an older row's partner: %ld by all rows, %ld by rows that have a partner themselves\n", olderAll, olderDoomed);
    std::printf("fam1 low levels (A1(q,r) < tau1(r)): %ld, at most %d per row; their values: partner of a younger row %ld, diagonal value %ld, partner of an older row %ld; rows with more low levels than n1(r): %ld\n", low, mostLow, lowYoung, lowDiag, lowOld, badL10); }
  { int s = 0, I = 0, lo = 1 << 30, hi = -(1 << 30); std::vector<int> cnt(H + 2, 0);
    for (int x = 0; x <= H; ++x) if (tau1[x] >= 0 && tau1[x] <= H) ++cnt[tau1[x]];
    for (int t = 1; t <= H; ++t) { if (tau1[t - 1] < 0) ++s; I += cnt[t]; lo = std::min(lo, s - I); hi = std::max(hi, s - I); }
    std::printf("fam1: s1(T-1) - I1(T) ranges over [%d,%d] for T <= %d\n", lo, hi, H); }
}
