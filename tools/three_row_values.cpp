// Unrestricted Grundy values of three-row Chomp, all values at once, and the values of the
// positions (omega,omega,x). This is tools/four_row_values.cpp without the fourth row; see
// notes/23 for the method and notes/30 for what it is used for.
//
// A position [a,b,x] has rows a >= b >= x. Unrestricted values: the poison may be taken, the
// empty position has value 0, a P-position of ordinary Chomp has value 1.
//
// A "row" is rho = (x,g), 0 <= x <= X, 1 <= g <= GM. It is born at level b = x. For b >= x,
//   A(b; rho) = the a >= b with G[a,b,x] = g, if no [j,j,min(x,j)] with j < b has value g.
// It is the least a >= max(b,1) that is not
//   * a value the row took at an earlier level;
//   * the birth value A(j; j, g) of a row (j,g), j < x;
//   * the value at the same level of an older row: (j,g) with j < x, or (x,g') with g' < g.
// The row dies at level b if A(b; rho) = b: then G[b,b,x] = g. It is stillborn if a row (j,g),
// j < x, died at its own birth level (then G[j,j,j] = g). All of this is exact.
//
// With F(x) = { g : row (x,g) dies or is stillborn },
//   G(omega,omega,x) = mex( {0} u F(x) u { G(omega,omega,j) : j < x } ).
// "Never dies" needs a certificate: if a set C of rows contains the older rows of its members
// and every row of C has the same state (dead or not; the set of v - b for its earlier values
// v >= b) at the start of the levels T - P and T, then no row of C alive at T ever dies
// (notes/23, Lemma 3).
//
// usage: three_row_values X GM T [P1,P2,...] [OUT]
//   Prints the values G(omega,omega,x) and G[x,x,x] with proofs where the certificate gives
//   them, the least value not attained, and statistics. OUT (optional, text) receives one line
//   per row: x g death birth, with death = -1 alive at T, -2 stillborn.
//   Environment: WORDS=w sets the window to 64*w values above the level (default 16).
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 4) { std::fprintf(stderr, "usage: three_row_values X GM T [P1,P2,...] [OUT]\n"); return 1; }
  const int X = std::atoi(argv[1]), GM = std::atoi(argv[2]), T = std::atoi(argv[3]);
  int W = 16;
  if (const char* e = std::getenv("WORDS")) W = std::atoi(e);
  if (W < 1 || W > 1024) { std::fprintf(stderr, "WORDS must be between 1 and 1024\n"); return 1; }
  const int NB = 64 * W;
  std::vector<int> lags;
  if (argc > 4)
    for (const char* q = argv[4]; *q;) {
      int v = std::atoi(q);
      if (v > 0) lags.push_back(v);
      while (*q && *q != ',') ++q;
      if (*q == ',') ++q;
    }
  for (int P : lags) if (T - P <= X) { std::fprintf(stderr, "need T - P > X\n"); return 1; }
  const size_t nrow = (size_t)(X + 1) * GM;
  auto rowIndex = [&](int x, int g) { return (size_t)x * GM + (g - 1); };

  // window of a living row: the values it took earlier, as bits v mod NB
  std::vector<uint64_t> pool(nrow * (size_t)W, 0);
  std::vector<int32_t> death(nrow, -1), birth(nrow, 0);
  std::vector<uint8_t> dead(nrow, 0), born(nrow, 0), still(GM, 0);
  std::vector<uint64_t> acc((size_t)GM * W), accG(W);
  std::vector<std::vector<uint64_t>> snaps(lags.size());
  std::vector<std::vector<uint8_t>> deadSnaps(lags.size());
  long long overflowMax = 0;
  bool failed = false;
  for (int b = 0; b < T && !failed; ++b) {
    for (size_t k = 0; k < lags.size(); ++k)
      if (b == T - lags[k]) { snaps[k] = pool; deadSnaps[k] = dead; }
    const int xmax = std::min(X, b);
    if (b <= X) {
      const int x = b;
      for (int g = 1; g <= GM; ++g) {
        const size_t r = rowIndex(x, g);
        if (still[g - 1]) { dead[r] = 1; death[r] = -2; continue; }
        born[r] = 1;
        uint64_t* o = &pool[r * W];
        for (int j = 0; j < x; ++j) {
          const int v = birth[rowIndex(j, g)];
          if (v >= b) {
            if (v - b >= NB) { failed = true; continue; }
            o[(v % NB) >> 6] |= 1ull << (v & 63);
          }
        }
      }
    }
    std::fill(acc.begin(), acc.end(), 0);
    const int s = b % NB, sw = s >> 6, sb = s & 63;
    const int prev = (b + NB - 1) % NB;
    for (int x = 0; x <= xmax; ++x) {
      std::fill(accG.begin(), accG.end(), 0);
      for (int g = 1; g <= GM; ++g) {
        const size_t r = rowIndex(x, g);
        if (dead[r]) continue;
        uint64_t* o = &pool[r * W];
        uint64_t* a3 = &acc[(size_t)(g - 1) * W];
        if (b > x) o[prev >> 6] &= ~(1ull << (prev & 63));
        long long off = -1;
        for (int k = 0; k <= W; ++k) {
          int i = sw + k;
          if (i >= W) i -= W;
          uint64_t w = o[i] | a3[i] | accG[i];
          if (k == 0) { w |= (1ull << sb) - 1; if (b == 0) w |= 1ull << sb; }
          if (k == W) w |= sb ? ~((1ull << sb) - 1) : ~0ull;
          if (w != ~0ull) { off = (long long)k * 64 + __builtin_ctzll(~w) - sb; break; }
        }
        if (off < 0) { failed = true; continue; }
        overflowMax = std::max(overflowMax, off);
        const int v = b + (int)off, p = v % NB;
        const uint64_t bit = 1ull << (p & 63);
        if (b == x) birth[r] = v;
        o[p >> 6] |= bit; a3[p >> 6] |= bit; accG[p >> 6] |= bit;
        if (off == 0) {
          dead[r] = 1; death[r] = b;
          if (b == x) still[g - 1] = 1;
        }
      }
    }
  }
  if (failed) { std::fprintf(stderr, "window overflow: raise WORDS\n"); return 1; }

  // certificate
  std::vector<uint8_t> cert(nrow, 0);
  std::vector<long long> certByLag(lags.size(), 0);
  for (size_t k = 0; k < lags.size(); ++k) {
    const int P = lags[k];
    const std::vector<uint64_t>& snap = snaps[k];
    const std::vector<uint8_t>& deadSnap = deadSnaps[k];
    const int s1 = (T - P) % NB, s2 = T % NB;
    auto rel = [&](const uint64_t* o, int s0, uint64_t* out) {
      const int w0 = s0 >> 6, b0 = s0 & 63;
      for (int i = 0; i < W; ++i) {
        uint64_t lo = o[(w0 + i) % W], hi = o[(w0 + i + 1) % W];
        out[i] = b0 ? (lo >> b0) | (hi << (64 - b0)) : lo;
      }
      out[W - 1] &= ~(1ull << 63);
    };
    std::vector<uint8_t> c3(GM, 1);                 // all rows (j,g), j < x, are certified
    std::vector<uint64_t> u1(W), u2(W);
    for (int x = 0; x <= X; ++x) {
      uint8_t cG = 1;
      for (int g = 1; g <= GM; ++g) {
        const size_t r = rowIndex(x, g);
        bool eq = dead[r] == deadSnap[r];
        if (eq && !dead[r]) {
          rel(&snap[r * W], s1, u1.data());
          rel(&pool[r * W], s2, u2.data());
          eq = std::memcmp(u1.data(), u2.data(), sizeof(uint64_t) * W) == 0;
        }
        const uint8_t c = deadSnap[r] ? 1 : (eq && c3[g - 1] && cG);
        if (c) { if (!cert[r] && !dead[r]) ++certByLag[k]; cert[r] = 1; }
        c3[g - 1] &= c; cG &= c;
      }
    }
  }

  // values of (omega,omega,x): gv = value if no row alive at T dies later; lb..ub proved bounds
  std::vector<int> gv(X + 1, 0), pv(X + 1, 0);
  std::vector<uint8_t> exact(X + 1, 0);
  {
    std::vector<uint8_t> hv(GM + 2, 0), ev(GM + 2, 0), nv(GM + 2, 1), nt(GM + 2);
    for (int x = 0; x <= X; ++x) {
      int v = GM + 1, lb = GM + 1, ub = GM + 2;
      for (int g = GM; g >= 1; --g) {
        const size_t r = rowIndex(x, g);
        const bool deadg = death[r] != -1;
        if (!(deadg || hv[g])) v = g;
        if (!(deadg || ev[g])) lb = g;
        if (!deadg && cert[r] && nv[g]) ub = g;
      }
      const bool ex = lb > GM || lb == ub;
      gv[x] = v; pv[x] = lb; exact[x] = ex;
      for (int g = 1; g <= GM; ++g) {
        const bool deadg = death[rowIndex(x, g)] != -1;
        nt[g] = deadg || ev[g] || g < lb || g > ub || (ex && g != lb);
      }
      if (v <= GM) hv[v] = 1;
      if (ex && lb <= GM) ev[lb] = 1;
      for (int g = 1; g <= GM; ++g) nv[g] &= nt[g];
    }
  }
  std::vector<int> firstInf(GM + 2, -1), firstInfExact(GM + 2, -1), firstRect(GM + 2, -1);
  std::printf("# x  G(w,w,x)  G[x,x,x]   (above %d shown as -; ? = not certified)\n", GM);
  for (int x = 0; x <= X; ++x) {
    int gi = gv[x], gr = -1;
    for (int g = 1; g <= GM; ++g) if (death[rowIndex(x, g)] == x) gr = g;
    if (x == 0) gr = 0;
    if (gi <= GM && firstInf[gi] < 0) firstInf[gi] = x;
    if (gi <= GM && exact[x] && firstInfExact[gi] < 0) firstInfExact[gi] = x;
    if (gr >= 1 && firstRect[gr] < 0) firstRect[gr] = x;
    {
      std::printf("%d ", x);
      if (gi <= GM) std::printf("%d%s ", gi, exact[x] ? "" : "?"); else std::printf("-%s ", exact[x] ? "" : "?");
      if (gr >= 0) std::printf("%d\n", gr); else std::printf("-\n");
    }
  }
  int mexL = 1, mexExact = 1, lastWitness = 0, lastWitnessExact = 0;
  for (int g = 1; g <= GM; ++g) {
    if (mexL == g && (firstInf[g] >= 0 || firstRect[g] >= 0)) { ++mexL; lastWitness = std::max(lastWitness, firstRect[g] >= 0 ? firstRect[g] : firstInf[g]); }
    if (mexExact == g && (firstInfExact[g] >= 0 || firstRect[g] >= 0)) { ++mexExact; lastWitnessExact = std::max(lastWitnessExact, firstRect[g] >= 0 ? firstRect[g] : firstInfExact[g]); }
  }
  std::printf("# least value not attained for x <= %d: %d%s (largest witness x = %d); least value without a certified witness: %d (largest witness x = %d)\n",
              X, mexL, mexL > GM ? " (above GM)" : "", lastWitness, mexExact, lastWitnessExact);
  long long nCertAlive = 0, nAlive = 0, nExact = 0;
  for (size_t r = 0; r < nrow; ++r) if (born[r] && !dead[r]) { ++nAlive; nCertAlive += cert[r]; }
  for (int x = 0; x <= X; ++x) nExact += exact[x];
  for (size_t k = 0; k < lags.size(); ++k) std::printf("# period %d certifies %lld more rows alive at T\n", lags[k], certByLag[k]);
  std::printf("# certified: %lld of %lld rows alive at T; %lld of %d values G(w,w,x) proved\n", nCertAlive, nAlive, nExact, X + 1);
  long long died = 0, stillb = 0, afterBirth = 0; int lastDeath = 0, lastX = 0, lastG = 0;
  for (int x = 0; x <= X; ++x)
    for (int g = 1; g <= GM; ++g) {
      const size_t r = rowIndex(x, g);
      if (death[r] == -2) { ++stillb; continue; }
      if (death[r] < 0) continue;
      ++died;
      if (death[r] > lastDeath) { lastDeath = death[r]; lastX = x; lastG = g; }
      if (death[r] > birth[r]) ++afterBirth;
    }
  std::printf("# rows: %lld died, %lld stillborn, %lld alive at T=%d; latest death at level %d, row (%d,%d); %lld rows died after their own birth value; largest offset used: %lld of %d\n",
              died, stillb, nAlive, T, lastDeath, lastX, lastG, afterBirth, overflowMax, NB);
  if (argc > 5) {
    FILE* f = std::fopen(argv[5], "w");
    if (f) {
      for (int x = 0; x <= X; ++x) for (int g = 1; g <= GM; ++g) { const size_t r = rowIndex(x, g); std::fprintf(f, "%d %d %d %d\n", x, g, death[r], birth[r]); }
      std::fclose(f);
    }
  }
  return 0;
}
