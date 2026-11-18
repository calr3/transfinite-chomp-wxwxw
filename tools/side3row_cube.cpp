// 3-row Chomp with one independent extra cell (the cube (0,1,0) of the (0,1)-tower family):
// [p,q,r | cube] is P iff the 2D position [p,q,r] has normal-play Grundy value 1.
//
// Two tables are computed together, stage by stage in the third row c (as in side3row.cpp):
//   A0(b,c): the unique a >= max(b,1) with [a,b,c] P (2D), or NONE;
//   A1(b,c): the unique a >= max(b,1) with [a,b,c | cube] P, or NONE.
// A1 follows the same rule as A0 with one more forbidden value: removing the cube from
// [a,b,c | cube] gives the 2D position [a,b,c], which is P iff a = A0(b,c). Row-1 cuts to
// [k,k,k | cube] (k <= c) must be N; the program stops if one is P.
// Both tables are kept (int32), so N is limited by memory (about 8 N^2/2 bytes).
//
// Output (for x <= N/2): "x tau0 tau1" with -1 for a side element of the respective family, then
// a defect classification for the cube family: for each partner p = tau1(z) and level q in
// (z,p): good (some b < z with A1(q,b) = p), ablock (A0(q,z) = p: the cube-removal reply), or
// dead (neither).
// usage: side3row_cube N [Z]   (defects for z <= Z; default N/3)
//        RES=1 [ONLYRES=1] side3row_cube N Z   also count the sources of the defects (see below)
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>

int main(int argc, char** argv) {
  const int N = std::atoi(argv[1]);
  const int Z = argc > 2 ? std::atoi(argv[2]) : N / 3;
  const int K = N + 64;                        // offsets A - b stay below K (checked)
  const long long V = (long long)N + K + 128, VW = V / 64 + 2, RW = K / 64 + 3;
  std::vector<int32_t> A0((size_t)(N + 1) * (N + 1), -1), A1((size_t)(N + 1) * (N + 1), -1);
  auto at = [&](std::vector<int32_t>& T, int b, int c) -> int32_t& { return T[(size_t)b * (N + 1) + c]; };
  std::vector<uint64_t> row0((size_t)(N + 1) * RW, 0), row1((size_t)(N + 1) * RW, 0);
  std::vector<uint64_t> diag0(VW, 0), diag1(VW, 0), col0(VW, 0), col1(VW, 0);
  std::vector<int> tau0(N + 1, -1), tau1(N + 1, -1);
  auto setbit = [](uint64_t* w, long long i) { w[i >> 6] |= 1ull << (i & 63); };
  for (int c = 0; c <= N; ++c) {
    if (c >= 1) {
      if (at(A0, c - 1, c - 1) >= 0) setbit(diag0.data(), at(A0, c - 1, c - 1));
      if (at(A1, c - 1, c - 1) >= 0) setbit(diag1.data(), at(A1, c - 1, c - 1));
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
        int extra = fam ? at(A0, b, c) : -1;   // the cube-removal option forbids A0(b,c)
        long long w = w0, a = -1;
        uint64_t mask = (1ull << (b & 63)) - 1;
        if (b == 0) mask = 1;
        for (;;) {
          if (w - w0 >= RW) { std::fprintf(stderr, "offset overflow\n"); return 1; }
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
        if (a == b && b == c && b > 0 && fam == 1) { std::fprintf(stderr, "[%d,%d,%d | cube] is P: finite P cut\n", b, b, b); return 1; }
      }
    }
  }
  if (getenv("RES")) {
    // Sources of the defects (RES=1): for each partner p = tau1(z) and each level q in (z,p),
    // a "cube-removal-only reply" at q is a good level t > q (witness s < z, A1(t,s) = p) such that
    // [p,q,s | cube] has the 2D P-position [p,q,s] as an option (A0(q,s) = p) but no row-1 reply
    // inside (q,p) (A1(q,s) not in (q,p)). Slot counting (notes/12) needs one at the topmost
    // defect; here they are counted at every defect level and at the good levels.
    long parts = 0, deadTot = 0, ablockTot = 0, ownSrc = 0, srcAtGood = 0, deadNoOwn = 0;
    for (int z = 1; z <= Z; ++z) {
      int p = tau1[z]; if (p < 0 || p > N) continue;
      ++parts;
      std::vector<int> lev1(z, -1);
      for (int q = z + 1; q < p; ++q) for (int s = 0; s < z; ++s) if (at(A1, q, s) == p) lev1[s] = q;
      std::vector<char> good(p - z, 0);
      for (int s = 0; s < z; ++s) if (lev1[s] > 0) good[lev1[s] - z] = 1;
      for (int q = z + 1; q < p; ++q) {
        int src = 0;
        for (int s = 0; s < z; ++s) if (lev1[s] > q && at(A0, q, s) == p) { int u = at(A1, q, s); if (!(u > q && u < p)) ++src; }
        if (good[q - z]) { srcAtGood += src; continue; }
        if (at(A0, q, z) == p) ++ablockTot; else ++deadTot;
        if (src) ++ownSrc; else ++deadNoOwn;
      }
    }
    std::fprintf(stderr, "RES: z <= %d: %ld partners; defect levels: %ld dead, %ld ablock; with their own cube-removal-only reply %ld, without %ld; such replies at good levels %ld\n",
                 Z, parts, deadTot, ablockTot, ownSrc, deadNoOwn, srcAtGood);
    if (getenv("ONLYRES")) return 0;
  }
  for (int x = 0; x <= N / 2; ++x) std::printf("t %d %d %d\n", x, tau0[x], tau1[x]);
  long good = 0, ablock = 0, dead = 0, partners = 0;
  // good(z,q): some b < z with A1(q,b) = tau1(z). Walk each row q once: for b < q with
  // v = A1(q,b) a partner tau1(z), and b < z < q < v, level q of z is good.
  std::vector<int> partnerOf(2 * N + 200, -1);
  for (int z = 0; z <= N; ++z) if (tau1[z] >= 0 && tau1[z] < (int)partnerOf.size()) partnerOf[tau1[z]] = z;
  std::vector<std::vector<char>> isGood(Z + 1);
  for (int z = 0; z <= Z; ++z) if (tau1[z] > z) isGood[z].assign(tau1[z] - z, 0);
  for (int q = 1; q <= N; ++q) for (int b = 0; b < q; ++b) {
    int v = at(A1, q, b); if (v < 0 || v >= (int)partnerOf.size()) continue;
    int z = partnerOf[v]; if (z < 0 || z > Z) continue;
    if (b < z && z < q && q < v) isGood[z][q - z] = 1;
  }
  for (int z = 0; z <= Z; ++z) {
    int p = tau1[z]; if (p < 0 || p > N) continue;
    ++partners;
    for (int q = z + 1; q < p; ++q) {
      if (isGood[z][q - z]) { ++good; continue; }
      if (at(A0, q, z) == p) { ++ablock; std::printf("ablock z=%d p=%d q=%d\n", z, p, q); }
      else {
        ++dead;
        std::printf("dead z=%d p=%d q=%d k=%d", z, p, q, at(A1, q, z));
        // the cube-removal exception at level q: s < z with A0(q,s) = p, and the level t with A1(t,s) = p
        for (int s2 = 0; s2 < z; ++s2) if (at(A0, q, s2) == p) {
          int t = -1; for (int t2 = q + 1; t2 < p; ++t2) if (at(A1, t2, s2) == p) t = t2;
          std::printf("  exception s=%d (2D [%d,%d,%d] P), level t=%d", s2, p, q, s2, t);
        }
        // what else is P near the top: A1(q,z) for q' = q..p-1, and A0(q',z)
        std::printf("  | A1(q',z) q'=q..p-1:"); for (int q2 = q; q2 < p; ++q2) std::printf(" %d", at(A1, q2, z));
        std::printf("  | A0(q',z):"); for (int q2 = q; q2 < p; ++q2) std::printf(" %d", at(A0, q2, z));
        std::printf("  | tau0(z)=%d\n", tau0[z]);
      }
    }
  }
  // 2D side rows: is the eventual offset A0(b,s) - b constant, and equal to 1 + #(non-side x < s)?
  {
    int checked = 0, constant = 0, formula = 0, nonside = 0, firstBad = -1, shown = 0;
    for (int s = 0; s <= N / 8; ++s) {
      if (tau0[s] >= 0) { ++nonside; continue; }
      ++checked;
      int d = at(A0, N / 2, s) - N / 2; bool cst = true;
      for (int b = N / 2; b <= N; ++b) if (at(A0, b, s) - b != d) { cst = false; break; }
      if (cst) ++constant;
      if (cst && d == 1 + nonside) ++formula;
      else {
        if (firstBad < 0) firstBad = s;
        if (++shown <= 6) {  // describe the row: offsets at the end, and where it last differs from 1 + nonside
          int last = -1; for (int b = s; b <= N; ++b) if (at(A0, b, s) - b != 1 + nonside) last = b;
          std::fprintf(stderr, "   row %d: 1+nonside=%d, offset at N=%d, last b with a different offset: %d\n", s, 1 + nonside, at(A0, N, s) - N, last);
        }
      }
    }
    std::fprintf(stderr, "2D side rows s <= %d: %d checked, %d with constant offset on [N/2,N], %d equal to 1 + #(non-side < s); first exception s=%d\n",
                 N / 8, checked, constant, formula, firstBad);
  }
  // the other ingredients for the cube family
  std::vector<char> isPartner(3 * N, 0), isDiag(3 * N, 0);
  for (int z = 0; z <= N; ++z) if (tau1[z] >= 0) isPartner[tau1[z]] = 1;
  int worst = -1 << 30, coinc = 0, neither = 0, H = N / 2;
  for (int a = 0; a <= N; ++a) { int d = at(A1, a, a); if (d >= 0 && d < 3 * N) { isDiag[d] = 1; if (a <= H) worst = std::max(worst, d - (2 * a + 1)); } }
  for (int h = 1; h <= H; ++h) { if (isPartner[h] && isDiag[h]) { ++coinc; if (coinc <= 10) std::printf("coincidence h=%d\n", h); } if (!isPartner[h] && !isDiag[h]) ++neither; }
  std::fprintf(stderr, "cube family, h <= %d: partner&diagonal %d, neither %d; max A1(a,a) - (2a+1) = %d\n", H, coinc, neither, worst);
  std::fprintf(stderr, "cube family, z <= %d: %ld partners; levels good %ld, ablock %ld, dead %ld\n", Z, partners, good, ablock, dead);
}
