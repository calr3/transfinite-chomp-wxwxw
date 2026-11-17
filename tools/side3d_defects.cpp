// Anatomy of the defects in the 3D side-set argument (notes/12, "The 3D side sets").
// For the box □_g and each partner p = tau(z), classify each level q in (z,p):
//   good     : some b < z has [p,q,b] P (row-3 reply from [p,q,z]);
//   ablock   : no such b, but [p,q,z | R''] is P for a one-cut attachment R'' (box-cut reply);
//   dead     : neither; then [k,q,z] is P for k = f(q,z) in (q,p) (row-1 reply).
// For each dead q also count alpha_q: good levels t in (q,p) whose position [p,q,s_t] has no
// row-1 P reply (only a box-cut one), i.e. the "slots" a dead level can use.
// usage: side3d_defects g ZMAX
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include "rod.h"
using namespace rod;

int main(int argc, char** argv) {
  int g = std::atoi(argv[1]), ZMAX = std::atoi(argv[2]);
  RodSolver S("333");
  auto rest = [&](int q, int r) {
    H h(9, 0);
    h[1] = h[2] = (uint8_t)g;
    h[3] = (uint8_t)q; h[4] = h[5] = (uint8_t)std::min(g, q);
    h[6] = (uint8_t)r; h[7] = h[8] = (uint8_t)std::min(g, r);
    return h;
  };
  auto F = [&](int q, int r) -> int { uint16_t v = S.f(rest(q, r)); return v == NONE ? -1 : v; };
  auto boxCutP = [&](int p, int q, int r) {  // some cut inside the box of [p,q,r] gives a P-position
    H base = rest(q, r);
    for (int c : {1, 2, 4, 5, 7, 8}) for (int t = 0; t < base[c]; ++t) if (S.f(S.cut(base, c, t)) == p) return true;
    return false;
  };
  const int HMAX = 254;
  std::vector<int> tau(ZMAX + 1, -1);
  for (int z = g; z <= ZMAX; ++z) for (int h = z + 1; h <= HMAX; ++h) if (F(h, z) == h) { tau[z] = h; break; }
  long nGood = 0, nAblock = 0, nDead = 0;
  std::printf("z: p=tau(z) | ablock levels | dead levels (alpha_q)\n");
  for (int z = g; z <= ZMAX; ++z) {
    int p = tau[z]; if (p < 0) continue;
    std::vector<int> s(p + 1, -1);   // s[q] = row b < z with F(q,b) = p, or -1
    std::vector<char> st(p + 1, 0);  // 0 good, 1 ablock, 2 dead
    for (int q = z + 1; q < p; ++q) {
      for (int b = 0; b < z; ++b) if (F(q, b) == p) { s[q] = b; break; }
      if (s[q] >= 0) { st[q] = 0; ++nGood; }
      else if (boxCutP(p, q, z)) { st[q] = 1; ++nAblock; }
      else { st[q] = 2; ++nDead; }
    }
    bool any = false;
    for (int q = z + 1; q < p; ++q) if (st[q]) any = true;
    if (!any) continue;
    std::printf("z=%d: p=%d |", z, p);
    for (int q = z + 1; q < p; ++q) if (st[q] == 1) std::printf(" %d", q);
    std::printf(" |");
    for (int q = z + 1; q < p; ++q) if (st[q] == 2) {
      int alpha = 0;
      for (int t = q + 1; t < p; ++t) {
        if (st[t] != 0) continue;
        // does [p,q,s_t] have a row-1 P reply [u,q,s_t], q < u < p ?
        int u = F(q, s[t]);
        if (!(u > q && u < p)) ++alpha;
      }
      std::printf(" %d(k=%d,a=%d)", q, F(q, z), alpha);
    }
    std::printf("\n");
  }
  std::printf("levels: good %ld, ablock %ld, dead %ld\n", nGood, nAblock, nDead);
}
