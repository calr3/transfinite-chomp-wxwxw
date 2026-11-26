// Three-row Chomp, all values at once: statistics on the rows (x,g) that die, value by value
// (notes/30). The recurrence is that of tools/three_row_values.cpp; this program keeps the
// whole history of each living row, so it is slower and meant for x up to about 1000.
//
// For a row (r,g) that dies at level p (G[p,p,r] = g, p > r) it records
//   * whether p exceeds its own birth value (the a with G[a,r,r] = g), or the birth value of a
//     row (a,g) with r < a < p: violations of (H4) of notes/19;
//   * whether p is the birth value of a younger row (an "overlap");
//   * its low levels: the levels q in (r,p) at which its value is below p, and what that value
//     is: the death level of an older row of the same value, of a younger one, or another value;
//   * for every level q in (r,p), who takes the value p at level q: an older row (b,g), b < r;
//     else a row (r,h), h < g; else a row (b,h) with b < r and h < g; else a younger row (b,g),
//     b > r; else none of these.
// It also counts the newborn rows whose birth value is not the largest value of their layer
// at that level (Sheiner's Lemma 4.1 for g = 1).
//
// usage: three_row_layers X GM T [XMIN]     rows with XMIN <= x <= X are reported
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 4) { std::fprintf(stderr, "usage: three_row_layers X GM T [XMIN]\n"); return 1; }
  const int X = std::atoi(argv[1]), GM = std::atoi(argv[2]), T = std::atoi(argv[3]);
  const int XMIN = argc > 4 ? std::atoi(argv[4]) : 0;
  const int NB = 8192;
  const size_t nrow = (size_t)(X + 1) * GM;
  auto row = [&](int x, int g) { return (size_t)x * GM + (g - 1); };
  std::vector<std::vector<uint8_t>> R(nrow);            // reserved offsets
  std::vector<std::vector<int>> picks(nrow);            // values at the levels x, x+1, ...
  std::vector<int> death(nrow, -1), birth(nrow, -1), cur(nrow, -1);
  std::vector<uint8_t> born(nrow, 0), still(GM, 0);
  const int VM = T + NB + 2;
  std::vector<std::vector<int>> deathAt(GM + 1, std::vector<int>(VM, -1)), birthOf(GM + 1, std::vector<int>(VM, -1));
  // taker[g][v] = (level, x) of the rows of layer g that took the value v
  std::vector<std::vector<std::vector<std::pair<int, int>>>> taker(GM + 1, std::vector<std::vector<std::pair<int, int>>>(VM));
  struct Stat { long long nb = 0, notMax = 0, nPart = 0, alive = 0, h4 = 0, overlap = 0, low = 0, lowOlder = 0, lowYounger = 0, lowOther = 0,
                levels = 0, tX = 0, tG = 0, tBoth = 0, tYoung = 0, tNone = 0; int maxLow = 0, maxOlder = 0; };
  std::vector<Stat> st(GM + 1);
  std::vector<int> pickedBy(NB + 2);
  for (int b = 0; b < T; ++b) {
    const int xmax = std::min(X, b);
    if (b <= X) for (int g = 1; g <= GM; ++g) {
      const size_t r = row(b, g);
      if (still[g - 1]) { death[r] = -2; continue; }
      born[r] = 1; R[r].assign(NB, 0);
      for (int j = 0; j < b; ++j) { const int v = birth[row(j, g)]; if (v >= b) { if (v - b >= NB) { std::fprintf(stderr, "overflow\n"); return 1; } R[r][v - b] = 1; } }
    }
    for (int g = 1; g <= GM; ++g) {
      std::fill(pickedBy.begin(), pickedBy.end(), -1);
      int largest = 0;
      for (int x = 0; x <= xmax; ++x) {
        const size_t r = row(x, g);
        if (!born[r] || death[r] != -1) { cur[r] = -1; continue; }
        std::vector<uint8_t>& o = R[r];
        int pick = 0;
        for (;; ++pick) {
          if (pick >= NB) { std::fprintf(stderr, "overflow\n"); return 1; }
          if (o[pick] || (b == 0 && pick == 0)) continue;
          if (pickedBy[pick] >= 0) continue;
          bool bg = false;
          for (int h = 1; h < g && !bg; ++h) if (cur[row(x, h)] == pick) bg = true;
          if (!bg) break;
        }
        if (b == x) {
          birth[r] = b + pick; birthOf[g][b + pick] = x;
          if (x >= XMIN) { ++st[g].nb; if (pick < largest) ++st[g].notMax; }
        }
        largest = std::max(largest, pick);
        cur[r] = pick; o[pick] = 1; pickedBy[pick] = x; picks[r].push_back(b + pick);
        if (pick > 0) taker[g][b + pick].push_back({b, x});
        if (pick == 0) {
          death[r] = b; deathAt[g][b] = x;
          if (b == x) still[g - 1] = 1;
          if (x >= XMIN && b > x) {
            Stat& s = st[g];
            ++s.nPart;
            int nl = 0, no = 0;
            for (size_t i = 0; i + 1 < picks[r].size(); ++i) {
              const int k = picks[r][i];
              if (k > b) continue;
              if (i == 0) continue;                       // the birth value: counted under (H4)
              ++nl;
              const int d = deathAt[g][k];
              if (d >= 0 && d < x) { ++s.lowOlder; ++no; } else if (d > x) ++s.lowYounger; else ++s.lowOther;
            }
            s.low += nl; s.maxLow = std::max(s.maxLow, nl); s.maxOlder = std::max(s.maxOlder, no);
            for (int a = x; a < b && a <= X; ++a) {
              const size_t ra = row(a, g);
              if (!born[ra]) continue;
              if (birth[ra] < b) ++s.h4;
              if (birth[ra] == b) ++s.overlap;
            }
            for (int q = x + 1; q < b; ++q) {
              ++s.levels;
              bool tx = false, tg = false, tb = false, ty = false;
              for (int h = 1; h <= g; ++h)
                for (const auto& lx : taker[h][b]) if (lx.first == q) {
                  if (h == g && lx.second < x) tx = true; else if (h == g && lx.second > x) ty = true;
                  else if (h < g && lx.second == x) tg = true; else if (h < g && lx.second < x) tb = true;
                }
              if (tx) ++s.tX; else if (tg) ++s.tG; else if (tb) ++s.tBoth; else if (ty) ++s.tYoung; else ++s.tNone;
            }
          }
          std::vector<int>().swap(picks[r]); std::vector<uint8_t>().swap(R[r]);
        }
      }
    }
    for (int x = 0; x <= xmax; ++x) for (int g = 1; g <= GM; ++g) {
      const size_t r = row(x, g);
      if (!born[r] || death[r] != -1) continue;
      std::vector<uint8_t>& o = R[r];
      std::memmove(o.data(), o.data() + 1, NB - 1); o[NB - 1] = 0;
    }
  }
  for (int x = XMIN; x <= X; ++x) for (int g = 1; g <= GM; ++g) if (born[row(x, g)] && death[row(x, g)] == -1) ++st[g].alive;
  std::printf("# rows %d <= x <= %d, levels to %d; layers with fewer than 20 dying rows (rectangle values) are omitted\n", XMIN, X, T);
  std::printf("# g | rows that die | alive at the end | (H4) violations | overlaps | newborn not the largest (of births) | low levels (most per row) | of which: partner of an older row (most per row) / of a younger row / other | levels q in (r,p) | p taken by: older row of the layer / row (r,h) / row (b,h) below in both / younger row / none\n");
  Stat tot;
  for (int g = 1; g <= GM; ++g) {
    const Stat& s = st[g];
    if (s.nPart < 20) continue;
    std::printf("%d | %lld | %lld | %lld | %lld | %lld (%lld) | %lld (%d) | %lld (%d) / %lld / %lld | %lld | %lld / %lld / %lld / %lld / %lld\n", g, s.nPart, s.alive, s.h4, s.overlap, s.notMax, s.nb,
                s.low, s.maxLow, s.lowOlder, s.maxOlder, s.lowYounger, s.lowOther, s.levels, s.tX, s.tG, s.tBoth, s.tYoung, s.tNone);
    tot.nPart += s.nPart; tot.alive += s.alive; tot.h4 += s.h4; tot.overlap += s.overlap; tot.low += s.low; tot.lowOlder += s.lowOlder; tot.lowYounger += s.lowYounger; tot.lowOther += s.lowOther;
    tot.levels += s.levels; tot.tX += s.tX; tot.tG += s.tG; tot.tBoth += s.tBoth; tot.tYoung += s.tYoung; tot.tNone += s.tNone;
    tot.maxLow = std::max(tot.maxLow, s.maxLow); tot.maxOlder = std::max(tot.maxOlder, s.maxOlder);
  }
  std::printf("# all | %lld | %lld | %lld | %lld | - | %lld (%d) | %lld (%d) / %lld / %lld | %lld | %lld / %lld / %lld / %lld / %lld\n", tot.nPart, tot.alive, tot.h4, tot.overlap,
              tot.low, tot.maxLow, tot.lowOlder, tot.maxOlder, tot.lowYounger, tot.lowOther, tot.levels, tot.tX, tot.tG, tot.tBoth, tot.tYoung, tot.tNone);
  return 0;
}
