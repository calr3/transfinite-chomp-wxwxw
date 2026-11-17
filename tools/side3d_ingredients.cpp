// The ingredients of the side-class infinitude argument (notes/12) in 3D, for the (0,1) towers.
//
// Base 3x3, cell index x*3+y. With the box R = □_g on the cells (x,1),(x,2), the position
// [p,q,r] means heights (0,0)=p, (1,0)=q, (2,0)=r and every cell (x,y), y >= 1, at
// min(g, height of (x,0)). Its "rest" (all cells but the poison) is rest(q,r). The rod solver's
// exact f(rest) is the unique p >= max(rest) with [p,q,r] P, or NONE.
//
// Checks, for z in [g, ZMAX] (heights stay below 255):
//   tau(z)  = the h > z with [h,h,z] P (side set: none);
//   diag(a) = f(rest(a,a)) for a >= g;
//   (1) row-start propagation: for z not in the side set, p = tau(z), and every q with z < q < p,
//       some b < z has f(rest(q,b)) = p; the b are distinct; each b >= g is a side element or has
//       tau(b) > q;
//   (2) partners and diagonal values never coincide;
//   (3) diag(a) <= 2a + 1 (and how far from it);
//   (4) the finite cut [k,k,k] is N for g < k (no finite P cut of W(□_g)).
// usage: side3d_ingredients g ZMAX
#include <cstdio>
#include <cstdlib>
#include <map>
#include <set>
#include <vector>
#include <algorithm>
#include "rod.h"
using namespace rod;

int main(int argc, char** argv) {
  int g = std::atoi(argv[1]), ZMAX = std::atoi(argv[2]);
  RodSolver S("333");
  auto rest = [&](int q, int r) {
    H h(9, 0);
    h[1] = h[2] = (uint8_t)g;                      // column x = 0 above (0,0): p >= g always here
    h[3] = (uint8_t)q; h[4] = h[5] = (uint8_t)std::min(g, q);
    h[6] = (uint8_t)r; h[7] = h[8] = (uint8_t)std::min(g, r);
    return h;
  };
  auto F = [&](int q, int r) -> int { uint16_t v = S.f(rest(q, r)); return v == NONE ? -1 : v; };
  const int HMAX = 254;
  // (4) finite cuts
  int finiteP = -1;
  for (int k = g + 1; k <= HMAX && finiteP < 0; ++k) {
    H h = rest(k, k);
    if (S.f(h) == k) finiteP = k;
  }
  std::printf("g=%d: finite P cut of W(box): %s", g, finiteP < 0 ? "none up to 254\n" : "");
  if (finiteP >= 0) std::printf("at k=%d\n", finiteP);
  // tau
  std::vector<int> tau(ZMAX + 1, -2);  // -1: side (no partner <= HMAX), -2: unknown
  for (int z = g; z <= ZMAX; ++z) {
    tau[z] = -1;
    for (int h = z + 1; h <= HMAX; ++h) if (F(h, z) == h) { tau[z] = h; break; }
  }
  int side = 0; for (int z = g; z <= ZMAX; ++z) if (tau[z] < 0) ++side;
  std::printf("side set in [%d,%d]: %d elements (reliable while tau(z) <= 254)\n", g, ZMAX, side);
  // (1) row-start propagation
  long inst = 0, missing = 0, nondistinct = 0, notalive = 0, small = 0, viaRcut = 0;
  std::map<int, int> byRest;
  std::vector<std::pair<int,int>> perZ;
  bool verbose = argc > 3;
  for (int z = g; z <= ZMAX; ++z) {
    int p = tau[z]; if (p < 0) continue;
    std::vector<int> used;
    for (int q = z + 1; q < p; ++q) {
      ++inst; int bq = -1;
      for (int b = 0; b < z; ++b) if (F(q, b) == p) { bq = b; break; }
      if (bq < 0) {
        ++missing;
        // is p blocked instead by a cut inside the attachment: some option [p,q,z | R'] P?
        H base = rest(q, z); bool viaR = false;
        for (int c : {1, 2, 4, 5, 7, 8}) for (int t = 0; t < base[c] && !viaR; ++t) {
          H h2 = S.cut(base, c, t); if (S.f(h2) == p) { viaR = true; ++viaRcut; byRest[(int)(h2[1]*100 + h2[2]*10 + h2[4])]++; }
        }
        if (!viaR && verbose) std::printf("   unexplained: z=%d p=%d q=%d\n", z, p, q);
        continue;
      }
      used.push_back(bq);
      if (bq < g) { ++small; continue; }
      if (!(tau[bq] < 0 || tau[bq] > q)) ++notalive;
    }
    std::sort(used.begin(), used.end());
    if (std::adjacent_find(used.begin(), used.end()) != used.end()) ++nondistinct;
    int defects = (p - z - 1) - (int)used.size();
    perZ.push_back({z, defects});
  }
  {
    int mx = 0, mz = -1, unexpl = 0; long tot = 0;
    for (auto [z, d] : perZ) { tot += d; if (d > mx) { mx = d; mz = z; } }
    std::printf("defects per z (q in (z,tau(z)) without a row b_q): max %d (at z=%d), total %ld over %zu non-side z\n", mx, mz, tot, perZ.size());
    std::printf("   by z:"); for (auto [z, d] : perZ) if (d) std::printf(" %d:%d", z, d); std::printf("\n");
    (void)unexpl;
  }
  std::printf("(1) row-start propagation: %ld instances, missing b %ld (of which blocked by a cut inside the box: %ld), non-distinct %ld, b >= g not alive %ld, b < g %ld\n",
              inst, missing, viaRcut, nondistinct, notalive, small);
  // per z: how many q used an attachment cut (should be bounded by the number of attachments)
  if (verbose) for (auto& [k, v] : byRest) std::printf("   attachment after cut %d: %d times\n", k, v);
  // (2),(3) diagonal values
  std::set<int> partners; for (int z = g; z <= ZMAX; ++z) if (tau[z] >= 0) partners.insert(tau[z]);
  int coincide = 0, worst = -1 << 30, undefined = 0;
  std::set<int> diag;
  for (int a = g; a <= HMAX / 2; ++a) {
    int d = F(a, a);
    if (d < 0) { ++undefined; continue; }
    diag.insert(d);
    if (partners.count(d)) {
      ++coincide;
      int zz = -1; for (int z = g; z <= ZMAX; ++z) if (tau[z] == d) zz = z;
      std::printf("   coincidence: diag(%d) = %d = tau(%d)\n", a, d, zz);
    }
    worst = std::max(worst, d - (2 * a + 1));
  }
  std::printf("(2) partner = diagonal value: %d cases;  (3) max diag(a) - (2a+1) for g <= a <= %d: %d (undefined: %d)\n",
              coincide, HMAX / 2, worst, undefined);
  // every h in (g, 254] a partner or a diagonal value?
  int HN = std::min(HMAX / 2, ZMAX);  // diagonal values are complete up to HMAX/2
  int neither = 0; for (int h = 2 * g + 2; h <= HN; ++h) if (!partners.count(h) && !diag.count(h)) ++neither;
  std::printf("h in (2g+1, %d] neither partner nor diagonal value: %d\n", HN, neither);
  std::fprintf(stderr, "[%lld f-values]\n", S.fcount);
}
