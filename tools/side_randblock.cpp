// The three-row recurrence with one random extra blocked value per cell (notes/19, section 8).
//
// A(b,c) is computed as in side3row.cpp: the least a >= max(b,1) outside the blocked set
// E(b,c). In addition, at each cell independently with probability rho/1000, the value the
// recurrence would take is forbidden and the next free value is taken instead. This models a
// family with one extra option per position (such as the cube family, where the extra blocked
// value is the 2D value A0(b,c)) but without any structure in the blocked values.
//
// Every statement of Sheiner's lemmas that survives for the cube family (distinct values in a
// row and in a level, at most one exception per level in the interval-blocking lemma) also
// holds here. The output shows that this is not enough to bound the defects of a partner: a row
// can behave like a side row for a long time and then die, and then almost all its levels are
// dead levels.
//
// For each row z <= N/2 with a partner p = tau(z) <= N: a level q in (z,p) is good if some row
// b < z has A(q,b) = p, blocked if the forbidden value at (q,z) was p, and dead otherwise.
// usage: side_randblock N rho [seed]
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <random>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 3) { std::fprintf(stderr, "usage: side_randblock N rho [seed]\n"); return 1; }
  const int N = std::atoi(argv[1]), rho = std::atoi(argv[2]); const unsigned seed = argc > 3 ? std::atoi(argv[3]) : 1;
  const int V = 3 * N + 100;
  std::mt19937 rng(seed);
  std::vector<int32_t> A((size_t)(N + 1) * (N + 1), -1), X((size_t)(N + 1) * (N + 1), -1);
  auto at = [&](int b, int c) -> int32_t& { return A[(size_t)b * (N + 1) + c]; };
  auto xt = [&](int b, int c) -> int32_t& { return X[(size_t)b * (N + 1) + c]; };
  std::vector<std::vector<uint64_t>> level(N + 1, std::vector<uint64_t>(V / 64 + 2, 0));
  std::vector<uint64_t> diag(V / 64 + 2, 0), col(V / 64 + 2, 0);
  std::vector<int> tau(N + 1, -1);
  auto get = [](const std::vector<uint64_t>& w, int i) { return (w[i >> 6] >> (i & 63)) & 1; };
  auto set = [](std::vector<uint64_t>& w, int i) { w[i >> 6] |= 1ull << (i & 63); };
  for (int c = 0; c <= N; ++c) {
    if (c >= 1 && at(c - 1, c - 1) >= 0) set(diag, at(c - 1, c - 1));
    std::fill(col.begin(), col.end(), 0);
    for (int b = c; b <= N; ++b) {
      int a = std::max(b, 1);
      auto blocked = [&](int v) { return get(level[b], v) || get(col, v) || get(diag, v); };
      while (blocked(a)) ++a;
      if ((int)(rng() % 1000) < rho) { xt(b, c) = a; ++a; while (blocked(a)) ++a; }
      at(b, c) = a; set(level[b], a); set(col, a);
      if (a == b && b > c) { tau[c] = b; break; }
      if (a == b && b == c && b > 0) { std::fprintf(stderr, "[%d,%d,%d] is P: finite P cut\n", b, b, b); return 1; }
    }
  }
  const int H = N / 2 - 2; long side = 0, parts = 0, lev = 0, good = 0, blockedLev = 0, dead = 0;
  int worstRow = -1, worstDead = 0, late = 0;
  for (int z = 1; z <= H; ++z) { int p = tau[z]; if (p < 0) { ++side; continue; } ++parts;
    if (p > 3 * z + 3) ++late;
    int def = 0;
    for (int q = z + 1; q < p; ++q) { ++lev; bool g = false;
      for (int s = 0; s < z && !g; ++s) g = at(q, s) == p;
      if (g) ++good; else if (xt(q, z) == p) ++blockedLev; else { ++dead; ++def; } }
    if (def > worstDead) { worstDead = def; worstRow = z; } }
  std::printf("N=%d rho=%d/1000 seed=%u: rows <= %d alive at level N: %ld (%.4f); partners %ld, of which %d have tau(z) > 3z+3\n",
              N, rho, seed, H, side, (double)side / H, parts, late);
  std::printf("  levels %ld: good %ld, blocked %ld, dead %ld; most dead levels of one partner: %d (row %d, tau = %d)\n",
              lev, good, blockedLev, dead, worstDead, worstRow, worstRow >= 0 ? tau[worstRow] : -1);
}
