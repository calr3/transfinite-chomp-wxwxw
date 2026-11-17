// Exact P-positions of 3-row Chomp with a finite attachment, for every attachment below a box.
//
// Base 3x3 (cells (x,y)), heights along z. A position [a,b,c | R]: cells (0,0),(1,0),(2,0) have
// heights a >= b >= c (the three "rows"), and the attachment R gives heights R(x,y) to the cells
// (x,1),(x,2): a 3x2 plane partition with R(x,y) <= the height of (x,0). Moves:
//   cut (0,0) at k: every cell capped at k;   cut (1,0) at k: columns x >= 1 capped at k;
//   cut (2,0) at k: column 2 capped at k;     cut (x,y), y >= 1, at t: cells (x',y') with
//   x' >= x, y' >= y capped at t (a move inside the attachment).
// For each (b, c, R) with R(1,.) <= b, R(2,.) <= c, A(b,c,R) is the unique a >= max(b, R(0,1), 1)
// with [a,b,c | R] P, or NONE when some cut of (0,0) below that range already wins (then every
// larger a is N). The tables for all attachments R <= box g are computed together:
//   * outer loop c (third row), inner loop b >= c, then attachments by increasing size;
//   * blocked values: row-3 cuts (accumulated per (b,R)), row-2 cuts and the diagonal (per
//     stage and attachment), and cuts inside the attachment (same (b,c), smaller attachment);
//   * NONE: a cut of (0,0) to some k < b gives a P-position: [k,k,k | R^k] (k <= c) or
//     [k,k,c | R^k] (c < k < b); and, for b < R(0,1), a cut to k in [b, R(0,1)) giving
//     [k,b,c | R^k] P (column 0 of the attachment then shrinks).
// Output for the box itself: partners tau(z) (the h > z with [h,h,z | box] P), side elements,
// diagonal values, finite P cuts; optional defect classification (see notes/12).
// usage: attach3row g N [Z [a01,a02,a11,a12,a21,a22]]
//   rows up to N; defects for partners of z <= Z (0 = none); the report is for the box, or for
//   the given attachment (entries <= g).
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <map>
#include <vector>

struct Att { int h[6]; int size; };  // order: (0,1),(0,2),(1,1),(1,2),(2,1),(2,2)
static int idxOf(int x, int y) { return 2 * x + (y - 1); }

int main(int argc, char** argv) {
  const int g = std::atoi(argv[1]), N = std::atoi(argv[2]), Z = argc > 3 ? std::atoi(argv[3]) : 0;
  const int dump = std::getenv("DUMP") ? std::atoi(std::getenv("DUMP")) : 0;  // debug: print A for b <= DUMP
  // all plane partitions with entries <= g
  std::vector<Att> att;
  std::map<std::vector<int>, int> id;
  for (int a01 = 0; a01 <= g; ++a01) for (int a02 = 0; a02 <= a01; ++a02)
  for (int a11 = 0; a11 <= a01; ++a11) for (int a12 = 0; a12 <= std::min(a11, a02); ++a12)
  for (int a21 = 0; a21 <= a11; ++a21) for (int a22 = 0; a22 <= std::min(a21, a12); ++a22) {
    Att t{{a01, a02, a11, a12, a21, a22}, a01 + a02 + a11 + a12 + a21 + a22};
    att.push_back(t);
  }
  std::sort(att.begin(), att.end(), [](const Att& u, const Att& v) { return u.size < v.size; });
  const int NA = att.size();
  for (int i = 0; i < NA; ++i) id[std::vector<int>(att[i].h, att[i].h + 6)] = i;
  auto find = [&](const int* h) { return id.at(std::vector<int>(h, h + 6)); };
  auto capCols = [&](int r, int x0, int k) {  // cap columns x >= x0 at k
    int h[6]; for (int i = 0; i < 6; ++i) h[i] = att[r].h[i];
    for (int x = x0; x < 3; ++x) for (int y = 1; y <= 2; ++y) h[idxOf(x, y)] = std::min(h[idxOf(x, y)], k);
    return find(h);
  };
  // one-cuts: distinct smaller attachments reached by one move inside the attachment
  std::vector<std::vector<int>> oneCuts(NA);
  for (int r = 0; r < NA; ++r) {
    std::vector<int> v;
    for (int x = 0; x < 3; ++x) for (int y = 1; y <= 2; ++y) for (int t = 0; t < att[r].h[idxOf(x, y)]; ++t) {
      int h[6]; for (int i = 0; i < 6; ++i) h[i] = att[r].h[i];
      for (int x2 = x; x2 < 3; ++x2) for (int y2 = y; y2 <= 2; ++y2) h[idxOf(x2, y2)] = std::min(h[idxOf(x2, y2)], t);
      int s = find(h); if (s != r) v.push_back(s);
    }
    std::sort(v.begin(), v.end()); v.erase(std::unique(v.begin(), v.end()), v.end());
    oneCuts[r] = v;
  }
  int box = NA - 1;  // the largest (all entries g), unless another attachment is asked for
  if (argc > 4) { int h[6]; std::sscanf(argv[4], "%d,%d,%d,%d,%d,%d", &h[0], &h[1], &h[2], &h[3], &h[4], &h[5]); box = find(h); }
  // capping tables for small heights (k < g); for k >= g capping changes nothing
  auto cap = [&](int r, int x0, int k) { return k >= g ? r : capCols(r, x0, k); };
  std::vector<std::vector<int>> capAll(g + 1, std::vector<int>(NA)), cap12(g + 1, std::vector<int>(NA)), cap2(g + 1, std::vector<int>(NA));
  for (int k = 0; k <= g; ++k) for (int r = 0; r < NA; ++r) { capAll[k][r] = cap(r, 0, k); cap12[k][r] = cap(r, 1, k); cap2[k][r] = cap(r, 2, k); }
  auto CA = [&](int r, int k) { return k >= g ? r : capAll[k][r]; };
  // preimages: preX[k][r] = all r2 with capX(r2, k) = r, for k < g
  std::vector<std::vector<std::vector<int>>> preAll(g), pre12(g), pre2(g);
  for (int k = 0; k < g; ++k) {
    preAll[k].assign(NA, {}); pre12[k].assign(NA, {}); pre2[k].assign(NA, {});
    for (int r = 0; r < NA; ++r) { preAll[k][capAll[k][r]].push_back(r); pre12[k][cap12[k][r]].push_back(r); pre2[k][cap2[k][r]].push_back(r); }
  }
  auto C12 = [&](int r, int k) { return k >= g ? r : cap12[k][r]; };
  auto C2 = [&](int r, int k) { return k >= g ? r : cap2[k][r]; };
  auto valid = [&](int r, int b, int c) { const int* h = att[r].h; return h[2] <= b && h[3] <= b && h[4] <= c && h[5] <= c; };

  const int K = N + 64;                       // offsets a - b (checked)
  const long long V = (long long)N + K + 128, VW = V / 64 + 2, RW = K / 64 + 3;
  // full table is too big; keep: rows' row-3 sets (bitsets), the current stage's values per (b,R),
  // diagonal values, and (if defects are wanted) the full table for the box's relevant families.
  std::vector<uint64_t> rowbits((size_t)(N + 1) * NA * RW, 0);
  std::vector<uint64_t> colbits((size_t)NA * VW, 0), diagbits((size_t)NA * VW, 0);
  std::vector<int> Adiag((size_t)(N + 1) * NA, -1);
  std::vector<int> stageVal((size_t)(N + 1) * NA, -1);  // A(b, c, R) for the current stage c
  std::vector<int> prevStage;                            // not needed
  // full table for defects, only for the families the check reads: the target's column-2
  // cappings and its one-cut attachments (int16, b <= Nd)
  const int Nd = Z > 0 ? std::min(N, 2 * Z + 64) : -1;
  std::vector<int> slot(NA, -1); int nslot = 0;
  if (Nd > 0) {
    for (int bb = 0; bb <= g; ++bb) { int r = C2(box, bb); if (slot[r] < 0) slot[r] = nslot++; }
    for (int s2 : oneCuts[box]) if (slot[s2] < 0) slot[s2] = nslot++;
  }
  std::vector<int16_t> full;
  if (Nd > 0) full.assign((size_t)(Nd + 1) * (Nd + 1) * nslot, -1);
  auto FULLGET = [&](int b, int c, int r) -> int { return full[((size_t)b * (Nd + 1) + c) * nslot + slot[r]]; };
  std::vector<int> tau((size_t)(N + 1) * NA, -1);        // tau[c*NA + R]: the k with A(k,c,R) = k, k > c
  std::vector<char> finiteP((size_t)(N + 1) * NA, 0);    // [k,k,k | R] P
  std::vector<int> finCut(NA, 1 << 30);                  // least k with [k,k,k | R^k] P
  auto setb = [](uint64_t* w, long long i) { w[i >> 6] |= 1ull << (i & 63); };
  auto getb = [](const uint64_t* w, long long i) { return (w[i >> 6] >> (i & 63)) & 1; };

  for (int c = 0; c <= N; ++c) {
    // diagonal sets: add A(c-1, c-1, cap12(R, c-1)) to every R's set
    if (c >= 1) for (int r = 0; r < NA; ++r) { int v = Adiag[(size_t)(c - 1) * NA + C12(r, c - 1)]; if (v >= 0) setb(&diagbits[(size_t)r * VW], v); }
    std::fill(colbits.begin(), colbits.end(), 0);
    // NONE thresholds: finite cuts [k,k,k | R^k], k < c (persistent), then this stage's partners
    std::vector<int> noneFrom(finCut);
    for (int b = c; b <= N; ++b) {
      for (int r = 0; r < NA; ++r) {
        if (!valid(r, b, c)) continue;
        int v = -1;
        if (noneFrom[r] < b) { stageVal[(size_t)b * NA + r] = -1; goto store; }
        {
          // for b < R(0,1): a cut of (0,0) to k in [max(b,1), R(0,1)) shrinks column 0
          int r01 = att[r].h[0];
          bool none2 = false;
          for (int k = std::max(b, 1); k < r01 && !none2; ++k) if (stageVal[(size_t)b * NA + CA(r, k)] == k) none2 = true;
          if (none2) { v = -1; goto store; }
          long long lo = std::max({b, r01, 1});
          const uint64_t* row = &rowbits[((size_t)b * NA + r) * RW];
          const uint64_t* col = &colbits[(size_t)r * VW];
          const uint64_t* dg = &diagbits[(size_t)r * VW];
          long long w0 = b >> 6, w = lo >> 6;
          uint64_t mask = (1ull << (lo & 63)) - 1;
          for (;;) {
            if (w - w0 >= RW) { std::fprintf(stderr, "offset overflow\n"); return 1; }
            uint64_t x = row[w - w0] | col[w] | dg[w] | mask;
            for (int s : oneCuts[r]) { int u = stageVal[(size_t)b * NA + s]; if (valid(s, b, c) && u >= 0 && (u >> 6) == w) x |= 1ull << (u & 63); }
            if (x != ~0ull) { v = w * 64 + __builtin_ctzll(~x); break; }
            mask = 0; ++w;
          }
        }
      store:
        stageVal[(size_t)b * NA + r] = v;
        if (dump && b <= dump) std::printf("A %d %d %d,%d,%d,%d,%d,%d %d\n", b, c, att[r].h[0], att[r].h[1], att[r].h[2], att[r].h[3], att[r].h[4], att[r].h[5], v);
        if (Nd > 0 && b <= Nd && slot[r] >= 0) full[((size_t)b * (Nd + 1) + c) * nslot + slot[r]] = (int16_t)v;
        if (v < 0) continue;
        // later row-3 sets: rows b, families R' with cap2(R', c) = r (c >= g: R' = r)
        if (c >= g) setb(&rowbits[((size_t)b * NA + r) * RW], v - 64LL * (b >> 6));
        else for (int r2 : pre2[c][r]) setb(&rowbits[((size_t)b * NA + r2) * RW], v - 64LL * (b >> 6));
        // this stage's row-2 sets: families R' with cap12(R', b) = r
        if (b >= g) setb(&colbits[(size_t)r * VW], v);
        else for (int r2 : pre12[b][r]) setb(&colbits[(size_t)r2 * VW], v);
        if (b == c) {
          Adiag[(size_t)b * NA + r] = v;
          if (v == b && b >= 1) {
            finiteP[(size_t)b * NA + r] = 1;
            // [b,b,b | r] is P: for larger second rows in this stage, families R' with
            // capAll(R', b) = r are NONE (cut (0,0) at b)
            if (b >= g) noneFrom[r] = std::min(noneFrom[r], b);
            else for (int r2 : preAll[b][r]) noneFrom[r2] = std::min(noneFrom[r2], b);
            if (b >= g) finCut[r] = std::min(finCut[r], b);
            else for (int r2 : preAll[b][r]) finCut[r2] = std::min(finCut[r2], b);
          }
        }
        if (v == b && b > c) {
          tau[(size_t)c * NA + r] = b;
          // NONE from here on for families R' with capAll(R', b) = r
          if (b >= g) noneFrom[r] = std::min(noneFrom[r], b);
          else for (int r2 : preAll[b][r]) noneFrom[r2] = std::min(noneFrom[r2], b);
        }
      }
    }
  }
  // Two-wide stalks S(z,R): (0,0) and (1,0) infinite, (2,0) at z, attachment R (column 2 <= z).
  // S(z,R) is P iff no option is P. Options: a cut of (0,0) at h gives [h,h,z | R^h] (h > z) or
  // [h,h,h | R^h] (h <= z); a cut of (1,0) leaves one infinite column (N); a cut of (2,0) at
  // z' < z gives S(z', cap2(R,z')); a cut inside R gives S(z, R'') for a one-cut R''.
  // Reliable for z <= Zs = N/2 (partners tau_R(z) are about 1.4 z).
  const int Zs = std::getenv("ZSTALK") ? std::atoi(std::getenv("ZSTALK")) : N / 2;
  std::vector<char> Sp((size_t)(Zs + 1) * NA, 0);
  std::vector<int> firstP(NA, -1), sigma(NA, -1);
  for (int z = 0; z <= Zs; ++z) for (int r = 0; r < NA; ++r) {
    if (att[r].h[4] > z || att[r].h[5] > z) continue;
    bool side = true;
    for (int h = z + 1; h < g && h <= N; ++h) if (tau[(size_t)z * NA + CA(r, h)] == h) side = false;
    { int t = tau[(size_t)z * NA + r]; if (t >= std::max(g, z + 1)) side = false; }
    if (!side || finCut[r] <= z) continue;
    bool lower = false;
    for (int z2 = 0; z2 < std::min(z, g); ++z2) if (Sp[(size_t)z2 * NA + C2(r, z2)]) lower = true;
    if (firstP[r] >= 0 && firstP[r] < z) lower = true;
    if (lower) continue;
    bool ac = false; for (int s2 : oneCuts[r]) if (Sp[(size_t)z * NA + s2]) ac = true;
    if (ac) continue;
    Sp[(size_t)z * NA + r] = 1;
    if (z >= g && firstP[r] < 0) firstP[r] = z;
    if (sigma[r] < 0) sigma[r] = z;
  }
  if (std::getenv("STALKDEBUG")) for (int z = 0; z <= std::min(Zs, g + 2); ++z) {
    int r = C2(box, z);
    bool side = true; int hit = -1;
    for (int h = z + 1; h < g && h <= N; ++h) if (tau[(size_t)z * NA + CA(r, h)] == h) { side = false; hit = h; }
    int t = tau[(size_t)z * NA + r];
    std::fprintf(stderr, "z=%d fam=%d,%d,%d,%d,%d,%d Sp=%d tau=%d smallhit=%d finCut=%d\n", z, att[r].h[0], att[r].h[1], att[r].h[2], att[r].h[3], att[r].h[4], att[r].h[5],
                 Sp[(size_t)z * NA + r], t, hit, finCut[r] > N ? -1 : finCut[r]);
  }
  // closed class W(R) (row y = 0 infinite): D(R) = some finite or two-wide option is P.
  // W(R) is P iff not D(R) and every one-cut W(R'') is N; if D holds everywhere, all W(R) are N.
  {
    int withD = 0, viaStalk = 0, viaFinite = 0; std::vector<int> noD;
    for (int r = 0; r < NA; ++r) {
      bool fin = finCut[r] <= N, st = false;
      for (int z = 0; z <= Zs && !st; ++z) if (Sp[(size_t)z * NA + C2(r, z)]) st = true;
      if (fin || st) { ++withD; if (st) ++viaStalk; else ++viaFinite; } else noD.push_back(r);
    }
    std::fprintf(stderr, "closed class, all %d attachments <= box %d: D found for %d (two-wide %d, finite only %d); none found for %zu\n",
                 NA, g, withD, viaStalk, viaFinite, noD.size());
    for (size_t i = 0; i < noD.size() && i < 10; ++i) { const int* h = att[noD[i]].h; std::fprintf(stderr, "   no D found: %d,%d,%d,%d,%d,%d\n", h[0], h[1], h[2], h[3], h[4], h[5]); }
    // W(R)'s two-wide options are S(z, cap2(R,z)); P claims are candidates only: a partner
    // beyond the computed rows (they can be very deep for small z) would make a stalk N.
    int zt = -1; for (int z = 0; z <= Zs && zt < 0; ++z) if (Sp[(size_t)z * NA + C2(box, z)]) zt = z;
    std::fprintf(stderr, "target %d,%d,%d,%d,%d,%d: candidate two-wide P reply at z = %d, finite P cut at %d (search z <= %d, rows <= %d)\n",
                 att[box].h[0], att[box].h[1], att[box].h[2], att[box].h[3], att[box].h[4], att[box].h[5],
                 zt, finCut[box] <= N ? finCut[box] : -1, Zs, N);
  }
  // report for the box
  int fc = -1; for (int k = 1; k <= N; ++k) if (finiteP[(size_t)k * NA + CA(box, k)]) { fc = k; break; }
  std::printf("box g=%d (%d attachments), rows <= %d: finite P cut %d\n", g, NA, N, fc);
  int zlo = 0; for (int i = 0; i < 6; ++i) zlo = std::max(zlo, att[box].h[i]);
  for (int z = zlo; z <= N / 2; ++z) std::printf("t %d %d\n", z, tau[(size_t)z * NA + box]);
  // diagonal values of the box family and coincidences with partners
  std::vector<char> isP(2 * N + 200, 0), isD(2 * N + 200, 0);
  for (int z = zlo; z <= N; ++z) { int t = tau[(size_t)z * NA + box]; if (t >= 0) isP[t] = 1; }
  int worst = -1 << 30;
  for (int a = zlo; a <= N; ++a) { int d = Adiag[(size_t)a * NA + box]; if (d >= 0 && d < (int)isD.size()) { isD[d] = 1; if (a <= N / 2) worst = std::max(worst, d - (2 * a + 1)); } }
  int coinc = 0, neither = 0;
  for (int h = 2 * zlo + 2; h <= N / 2; ++h) { if (isP[h] && isD[h]) { ++coinc; std::printf("coincidence %d\n", h); } if (!isP[h] && !isD[h]) ++neither; }
  std::fprintf(stderr, "g=%d: coincidences %d, neither %d (h in (2g+1, %d]); max diag - (2a+1) = %d\n", g, coinc, neither, N / 2, worst);
  if (Nd > 0) {
    long good = 0, ablock = 0, dead = 0, parts = 0, maxPer = 0, maxPerLate = 0;
    for (int z = zlo; z <= Z; ++z) {
      int p = tau[(size_t)z * NA + box]; if (p < 0 || p > Nd) continue;
      ++parts; long per = 0;
      for (int q = z + 1; q < p; ++q) {
        bool gd = false;
        for (int bb = 0; bb < z && !gd; ++bb) { int r = C2(box, bb); if (FULLGET(q, bb, r) == p) gd = true; }
        if (gd) { ++good; continue; }
        ++per;
        bool ab = false; for (int s2 : oneCuts[box]) if (FULLGET(q, z, s2) == p) ab = true;
        if (ab) ++ablock; else ++dead;
      }
      maxPer = std::max(maxPer, per); if (z >= 4 * zlo) maxPerLate = std::max(maxPerLate, per);
      if (per) std::printf("defects z=%d p=%d: %ld\n", z, p, per);
    }
    std::fprintf(stderr, "g=%d defects for z <= %d: %ld partners, good %ld, box-cut %ld, dead %ld; max per partner %ld (%ld for z >= 4g)\n",
                 g, Z, parts, good, ablock, dead, maxPer, maxPerLate);
  }
}
