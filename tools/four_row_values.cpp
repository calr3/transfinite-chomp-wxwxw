// Unrestricted Grundy values of four-row Chomp, organised for Huddleston-Shurman's open value
// G(4 x omega) = mex(L),  L = { G(omega,omega,a,a), G(a,a,a,a) : a < omega }.
//
// A position [a,b,x,y] has rows a >= b >= x >= y. Unrestricted values: the poison may be taken,
// the empty position has value 0, a P-position of ordinary Chomp has value 1.
// G[a,b,x,y] = g  iff  the position plus a one-wide stalk of height g over the poison cell, in a
// third direction, is a P-position of ordinary Chomp. For fixed (b,x,y) the values G[a,b,x,y],
// a >= b, are distinct, so there is at most one such a. Call it A(b; x,y,g).
//
// A "row" is rho = (x,y,g), y <= x <= X, 1 <= g <= GM. It is born at level b = x. At level b,
//   A(b; rho) = least a >= max(b,1) that is not
//     * a value the row took at an earlier level (cuts of the second row to j, x <= j < b);
//     * the birth value A(j; j, min(y,j), g) of a truncated row, j < x (cuts to j < x);
//     * the value at the same level of an older row: (j, min(y,j), g) with j < x,
//       (x, j, g) with j < y, or (x, y, g') with g' < g  (cuts of rows 3, 4 and of the stalk).
// The row dies at level b if A(b; rho) = b: then G[b,b,x,y] = g, and no taller position
// [a,b',x,y], b' > b, has value g. A row is stillborn if a truncated row (j, min(y,j), g),
// j < x, died at its own birth level j (then G[j,j,j,min(y,j)] = g).
// All of this is exact. The program runs the levels b = 0..T-1 and records, for every row, the
// level at which it died, or that it was still alive at the end. See notes/23.
//
// The finite options of (omega,omega,x,y) are (omega,omega,x',y') with a smaller side and the
// cuts [t,t,min(t,x),min(t,y)]. So, with F(x,y) = { g : row (x,y,g) dies or is stillborn },
//   G(omega,omega,x,y) = mex( {G(omega,omega,x,j) : j < y} u {G(omega,omega,j,min(y,j)) : j < x}
//                             u F(x,y) u {0} ).
// A death is a finite fact. "Never dies" is not, and needs a certificate.
//
// Certificate. Above level X no row is born, and the rule at level b depends only on the
// differences value - b. So the state of the system at the start of level b is, for each row,
// whether it is dead and the set { v - b : v >= b a value it took earlier }. The program
// compares the states at the start of the levels T - P and T. Let C be the largest set of rows
// that have equal states at the two levels and is closed under "depends on" (the older rows
// listed above). C evolves on its own and deterministically, so it is periodic with period P
// from level T - P on, and every row of C alive at level T never dies. Those rows are
// "certified". P has to be a common multiple of the periods of the rows concerned. Several
// values of P can be given; a row is certified if one of them certifies it. In the runs so far
// the periods are of the form 2^i 3^j 5^k (DIAG=M prints them for small cases).
//
// Values. The value printed for G(omega,omega,x,y) is the mex above with F(x,y) taken as the
// rows dead or stillborn by level T. Proof rules: g is attained if the row (x,y,g) is dead or
// stillborn, or an option side has proved value g; g is not attained if the row (x,y,g) is
// certified and every option side is proved to have another value. With lb the least g not
// proved attained and ub the least g proved not attained, the value is proved if lb = ub, or
// if lb > GM ("above GM"). Unproved values are printed with a question mark.
// G(a,a,a,a) is always exact (it is a death at the birth level, or none up to GM).
//
// usage: four_row_values X GM T [P1,P2,...] [OUT]
//   P = 0 (default): no certificate. Otherwise T - P must exceed X. Prints G(omega,omega,a,a)
//   and G(a,a,a,a) for a <= X, the first a at which each value up to GM occurs, and statistics.
//   OUT (optional) receives the death levels as int32 in the order x, y <= x, g
//   (-1 alive at T, -2 stillborn).
//   Environment: WORDS=w sets the window of values above the level to 64*w (default 16, at
//   most 64; the program stops if it is too small); TARGET=g reports for which a the statement
//   "G(omega,omega,a,a) != g" is proved (default GM); DIAG=M prints the minimal periods of the
//   last M values of each row (memory 2M bytes per row); PROGRESS=n reports every n levels.
//   Compile with -fopenmp to use several cores; the output does not depend on it. BLOCK=B sets
//   the size of the blocks of sides that are processed in parallel (default 16). Memory: 14
//   bytes per row plus 8*WORDS bytes per row living at the same time (about 40% of the rows at
//   the peak); POOLFRAC=f reserves address space for a fraction f of the rows (default 0.5).
//   BIRTHS=path writes the birth values A(x; x,y,g) as int32, in the order of OUT (the value is
//   meaningless for a stillborn row).
//   Example (notes/23, Theorem 4): four_row_values 107 46 100000 23040
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 4) { std::fprintf(stderr, "usage: four_row_values X GM T [P1,P2,...] [OUT]\n"); return 1; }
  const int X = std::atoi(argv[1]), GM = std::atoi(argv[2]), T = std::atoi(argv[3]);
  int W = 16;                                   // window of 64*W values above the level
  if (const char* e = std::getenv("WORDS")) W = std::atoi(e);
  if (W < 1 || W > 64) { std::fprintf(stderr, "WORDS must be between 1 and 64\n"); return 1; }
  const int NB = 64 * W;
  std::vector<int> lags;                        // the periods P to try
  if (argc > 4)
    for (const char* q = argv[4]; *q;) {
      int v = std::atoi(q);
      if (v > 0) lags.push_back(v);
      while (*q && *q != ',') ++q;
      if (*q == ',') ++q;
    }
  for (int P : lags) if (T - P <= X) { std::fprintf(stderr, "need T - P > X\n"); return 1; }
  const size_t nside = (size_t)(X + 1) * (X + 2) / 2, nrow = nside * GM;
  auto sideIndex = [](int x, int y) { return (size_t)x * (x + 1) / 2 + y; };
  auto rowIndex = [&](int x, int y, int g) { return sideIndex(x, y) * GM + (g - 1); };

  // Each living row has a window of W words: the values it took earlier, as bits v mod NB.
  // Windows are allocated at birth and released at death.
  std::vector<uint64_t> pool;
  {
    double frac = 0.5;                          // address space reserved for the windows, as a
    if (const char* e = std::getenv("POOLFRAC")) frac = std::atof(e);   // fraction of all rows
    pool.reserve((size_t)(frac * (double)nrow) * W + ((size_t)1 << 20) * W);
  }
  std::vector<int32_t> slot(nrow, -1), freeSlots;
  int32_t nSlots = 0;
  long long peakLive = 0, live = 0;
  std::vector<int32_t> death(nrow, -1), birth(nrow, 0);
  std::vector<uint8_t> dead(nrow, 0);
  // the living rows of each side, as a list of their g (so that dead rows cost nothing)
  if (GM > 255) { std::fprintf(stderr, "GM must be at most 255\n"); return 1; }
  std::vector<uint8_t> liveG(nrow, 0), liveCnt(nside, 0);
  // stillborn flags: stillDiag[g] = some row (j,j,g) born so far died at birth;
  // stillLine[y][g] = some row (j, min(y,j), g) born so far died at birth
  std::vector<uint8_t> stillLine((size_t)(X + 1) * GM, 0), stillDiag(GM, 0);
  // accumulators of the values taken at the current level
  std::vector<uint64_t> acc3((size_t)(X + 1) * GM * W), acc4((size_t)(X + 1) * GM * W), diagAcc((size_t)GM * W);
  long long overflowMax = 0;
  int PROGRESS = 0;
  if (const char* e = std::getenv("PROGRESS")) PROGRESS = std::atoi(e);

  int DIAG = 0;                                 // DIAG=M: minimal periods of the last M values of each row
  if (const char* e = std::getenv("DIAG")) DIAG = std::atoi(e);
  std::vector<uint16_t> tailv(DIAG ? nrow * (size_t)DIAG : 0, 0);
  std::vector<std::vector<uint64_t>> snaps(lags.size());   // states at the start of the levels T - P
  std::vector<std::vector<int32_t>> slotSnaps(lags.size());
  std::vector<std::vector<uint8_t>> deadSnaps(lags.size());
  std::vector<int32_t> diedNow;                 // slots released at the current level
  // At a level, a side depends only on sides with smaller x or smaller y. So the sides are cut
  // into blocks of B x B, and the blocks of one anti-diagonal are processed in parallel
  // (OpenMP, if enabled).
  int B = 16;
  if (const char* e = std::getenv("BLOCK")) B = std::max(1, std::atoi(e));
  bool failed = false;
  for (int b = 0; b < T && !failed; ++b) {
    for (size_t k = 0; k < lags.size(); ++k)
      if (b == T - lags[k]) { snaps[k] = pool; slotSnaps[k] = slot; deadSnaps[k] = dead; }
    const int xmax = std::min(X, b);
    if (b <= X) {                               // births of the rows (b, y, g)
      const int x = b;
      for (int y = 0; y <= x; ++y)
        for (int g = 1; g <= GM; ++g) {
          const size_t r = rowIndex(x, y, g);
          const size_t fl = (size_t)y * GM + (g - 1);
          if ((x > y) ? stillLine[fl] : stillDiag[g - 1]) {   // rows (x',y,g), x' > x, inherit it
            dead[r] = 1; death[r] = -2; stillLine[fl] = 1;
            continue;
          }
          int32_t sl;
          if (!freeSlots.empty()) { sl = freeSlots.back(); freeSlots.pop_back(); }
          else { sl = nSlots++; if ((size_t)nSlots * W > pool.size()) pool.resize(pool.size() + ((size_t)1 << 20) * W + (size_t)(x + 1) * GM * W, 0); }
          slot[r] = sl; ++live;
          liveG[sideIndex(x, y) * GM + liveCnt[sideIndex(x, y)]++] = (uint8_t)g;
          std::fill(pool.begin() + (size_t)sl * W, pool.begin() + (size_t)(sl + 1) * W, 0);
        }
      peakLive = std::max(peakLive, live);
#pragma omp parallel for schedule(dynamic, 4)
      for (int y = 0; y <= x; ++y)
        for (int g = 1; g <= GM; ++g) {
          const size_t r = rowIndex(x, y, g);
          if (dead[r]) continue;
          uint64_t* o = &pool[(size_t)slot[r] * W];
          for (int j = 0; j < x; ++j) {          // birth values of the truncated rows
            const size_t t = rowIndex(j, std::min(y, j), g);
            if (death[t] == -2) continue;
            const int v = birth[t];
            if (v >= b) {
              if (v - b >= NB) { failed = true; continue; }
              o[(v % NB) >> 6] |= 1ull << (v & 63);
            }
          }
        }
    }
    uint64_t* const poolp = pool.data();
    std::fill(diagAcc.begin(), diagAcc.end(), 0);
    std::fill(acc4.begin(), acc4.begin() + (size_t)(xmax + 1) * GM * W, 0);
    const int s = b % NB, sw = s >> 6, sb = s & 63;
    const int prev = (b + NB - 1) % NB;         // the value b-1 leaves the window
    const int nblk = xmax / B + 1;
    for (int d = 0; d <= 2 * (nblk - 1); ++d) {
      const int Jlo = std::max(0, d - (nblk - 1)), Jhi = d / 2;
#pragma omp parallel for schedule(dynamic, 1) reduction(max : overflowMax) if (Jhi > Jlo)
      for (int J = Jlo; J <= Jhi; ++J)
      for (int x = (d - J) * B; x < std::min((d - J + 1) * B, xmax + 1); ++x)
      for (int y = J * B; y < std::min((J + 1) * B, x + 1); ++y) {
        uint64_t* a3 = &acc3[((size_t)y * GM) * W];
        uint64_t* a4 = &acc4[((size_t)x * GM) * W];
        if (x == y) std::memcpy(a3, diagAcc.data(), sizeof(uint64_t) * GM * W);   // rows (j,j,g), j < y
        uint64_t accG[64];
        std::fill(accG, accG + W, 0);
        const size_t sd = sideIndex(x, y), base = sd * GM;
        uint8_t* lg = &liveG[base];
        const int nl = liveCnt[sd];
        bool anyDeath = false;
        for (int ii = 0; ii < nl; ++ii) {
          const int g = lg[ii];
          const size_t r = base + (g - 1);
          uint64_t* a3g = a3 + (size_t)(g - 1) * W;
          uint64_t* a4g = a4 + (size_t)(g - 1) * W;
          if (ii + 2 < nl) __builtin_prefetch(poolp + (size_t)slot[base + lg[ii + 2] - 1] * W + sw, 1);
          uint64_t* o = poolp + (size_t)slot[r] * W;
          if (b > x) o[prev >> 6] &= ~(1ull << (prev & 63));
          // least free value >= max(b,1), scanning the circular window from position s
          long long off = -1;
          for (int k = 0; k <= W; ++k) {
            int i = sw + k;
            if (i >= W) i -= W;
            uint64_t w = o[i] | a3g[i] | a4g[i] | accG[i];
            if (k == 0) { w |= (1ull << sb) - 1; if (b == 0) w |= 1ull << sb; }
            if (k == W) w |= sb ? ~((1ull << sb) - 1) : ~0ull;
            if (w != ~0ull) { off = (long long)k * 64 + __builtin_ctzll(~w) - sb; break; }
          }
          if (off < 0) { failed = true; continue; }
          overflowMax = std::max(overflowMax, off);
          const int v = b + (int)off, p = v % NB;
          const uint64_t bit = 1ull << (p & 63);
          if (b == x) birth[r] = v;
          if (DIAG && b >= T - DIAG) tailv[r * (size_t)DIAG + (b - (T - DIAG))] = (uint16_t)off;
          o[p >> 6] |= bit;
          a3g[p >> 6] |= bit;
          a4g[p >> 6] |= bit;
          accG[p >> 6] |= bit;
          if (x == y) diagAcc[(size_t)(g - 1) * W + (p >> 6)] |= bit;
          if (off == 0) {                        // G[b,b,x,y] = g
            dead[r] = 1; death[r] = b;
#pragma omp critical
            diedNow.push_back(slot[r]);
            slot[r] = -1;
            anyDeath = true;
            if (b == x) {
              stillLine[(size_t)y * GM + (g - 1)] = 1;
              if (x == y) stillDiag[g - 1] = 1;
            }
          }
        }
        if (anyDeath) {
          int n2 = 0;
          for (int ii = 0; ii < nl; ++ii) if (!dead[base + lg[ii] - 1]) lg[n2++] = lg[ii];
          liveCnt[sd] = (uint8_t)n2;
        }
      }
    }
    live -= (long long)diedNow.size();
    freeSlots.insert(freeSlots.end(), diedNow.begin(), diedNow.end());
    diedNow.clear();
    if (PROGRESS && b % PROGRESS == 0) std::fprintf(stderr, "level %d: %lld living rows\n", b, live);
  }
  if (failed) { std::fprintf(stderr, "window overflow: raise WORDS\n"); return 1; }

  if (DIAG) {
    std::vector<long long> hist(DIAG / 2 + 2, 0);
    long long none = 0;
    for (size_t r = 0; r < nrow; ++r) {
      if (dead[r]) continue;
      const uint16_t* q = &tailv[r * (size_t)DIAG];
      int per = 0;
      for (int p = 1; p <= DIAG / 2 && !per; ++p) {
        bool ok = true;
        for (int i = 0; i + p < DIAG && ok; ++i) ok = q[i] == q[i + p];
        if (ok) per = p;
      }
      if (per) ++hist[per]; else ++none;
    }
    std::printf("# minimal period of the last %d values, rows alive at T: ", DIAG);
    for (int p = 1; p <= DIAG / 2; ++p) if (hist[p]) std::printf("%d:%lld ", p, hist[p]);
    std::printf("none:%lld\n", none);
  }

  // certificate: rows with equal states at the start of levels T - P and T, closed under dependence
  std::vector<uint8_t> cert(nrow, 0);
  std::vector<long long> certByLag(lags.size(), 0);
  for (size_t k = 0; k < lags.size(); ++k) {
    const int P = lags[k];
    const std::vector<uint64_t>& snap = snaps[k];
    const std::vector<int32_t>& slotSnap = slotSnaps[k];
    const std::vector<uint8_t>& deadSnap = deadSnaps[k];
    const int s1 = (T - P) % NB, s2 = T % NB;    // window origins at the two levels
    auto rel = [&](const uint64_t* o, int s0, uint64_t* out) {
      const int w0 = s0 >> 6, b0 = s0 & 63;
      for (int k = 0; k < W; ++k) {
        uint64_t lo = o[(w0 + k) % W], hi = o[(w0 + k + 1) % W];
        out[k] = b0 ? (lo >> b0) | (hi << (64 - b0)) : lo;
      }
      out[W - 1] &= ~(1ull << 63);               // the value just below the level has left the window
    };
    std::vector<uint8_t> c3((size_t)(X + 1) * GM, 1), cDiag(GM, 1), c4(GM, 1);
    for (int x = 0; x <= X; ++x) {
      std::fill(c4.begin(), c4.end(), 1);
      for (int y = 0; y <= x; ++y) {
        uint8_t* c3y = &c3[(size_t)y * GM];
        if (x == y) std::memcpy(c3y, cDiag.data(), GM);
        uint8_t cG = 1;
        for (int g = 1; g <= GM; ++g) {
          const size_t r = rowIndex(x, y, g);
          bool eq = dead[r] == deadSnap[r];
          if (eq && !dead[r]) {
            uint64_t u1[64], u2[64];
            rel(&snap[(size_t)slotSnap[r] * W], s1, u1);
            rel(&pool[(size_t)slot[r] * W], s2, u2);
            eq = std::memcmp(u1, u2, sizeof(uint64_t) * W) == 0;
          }
          // a row dead at both levels has no values, so nothing depends on what it depended on
          const uint8_t c = deadSnap[r] ? 1 : (eq && c3y[g - 1] && c4[g - 1] && cG);
          if (c) { cert[r] = 1; if (!dead[r]) ++certByLag[k]; }
          c3y[g - 1] &= c; c4[g - 1] &= c; cG &= c;
          if (x == y) cDiag[g - 1] &= c;
        }
      }
    }
  }

  // Values of (omega,omega,x,y). gv = the value if no row alive at T dies later. Proved facts:
  //   * g is attained if the row (x,y,g) is dead or stillborn, or an option has proved value g;
  //   * g is not attained if the row (x,y,g) is certified and every option is proved != g;
  //   lb = least g not proved attained (value >= lb), ub = least g proved not attained
  //   (value <= ub). The value is proved if lb = ub, or if lb > GM ("above GM").
  //   notv[side][g] = "value != g" is proved.
  const int GW = GM + 2;
  std::vector<int> gv(nside, 0), pv(nside, 0);
  std::vector<uint8_t> exact(nside, 0), notv(nside * (size_t)GW, 0);
  long long nExact = 0;
  {
    // accumulators over the options of a side: hv = some option has value g if nothing dies
    // later, ev = some option has proved value g, nv = every option is proved != g
    std::vector<uint8_t> hv3((size_t)(X + 1) * GW, 0), ev3((size_t)(X + 1) * GW, 0), nv3((size_t)(X + 1) * GW, 1);
    std::vector<uint8_t> hvD(GW, 0), evD(GW, 0), nvD(GW, 1), hv4(GW), ev4(GW), nv4(GW);
    for (int x = 0; x <= X; ++x) {
      std::fill(hv4.begin(), hv4.end(), 0); std::fill(ev4.begin(), ev4.end(), 0); std::fill(nv4.begin(), nv4.end(), 1);
      for (int y = 0; y <= x; ++y) {
        uint8_t* h3 = &hv3[(size_t)y * GW]; uint8_t* e3 = &ev3[(size_t)y * GW]; uint8_t* n3 = &nv3[(size_t)y * GW];
        if (x == y) { std::memcpy(h3, hvD.data(), GW); std::memcpy(e3, evD.data(), GW); std::memcpy(n3, nvD.data(), GW); }
        const size_t sd = sideIndex(x, y);
        int v = GM + 1, lb = GM + 1, ub = GM + 2;
        for (int g = GM; g >= 1; --g) {
          const size_t r = rowIndex(x, y, g);
          const bool deadg = death[r] != -1;
          if (!(deadg || h3[g] || hv4[g])) v = g;
          if (!(deadg || e3[g] || ev4[g])) lb = g;
          if (!deadg && cert[r] && n3[g] && nv4[g]) ub = g;
        }
        const bool ex = lb > GM || lb == ub;
        gv[sd] = v; pv[sd] = lb; exact[sd] = ex; nExact += ex;
        uint8_t* nt = &notv[sd * GW];
        for (int g = 1; g <= GM; ++g) {
          const bool deadg = death[rowIndex(x, y, g)] != -1;
          nt[g] = deadg || e3[g] || ev4[g] || g < lb || g > ub || (ex && g != lb);
        }
        if (v <= GM) { h3[v] = 1; hv4[v] = 1; if (x == y) hvD[v] = 1; }
        if (ex && lb <= GM) { e3[lb] = 1; ev4[lb] = 1; if (x == y) evD[lb] = 1; }
        for (int g = 1; g <= GM; ++g) {
          n3[g] &= nt[g]; nv4[g] &= nt[g];
          if (x == y) nvD[g] &= nt[g];
        }
      }
    }
  }
  int TARGET = GM;                               // report where "G(w,w,a,a) != TARGET" is not proved
  if (const char* e = std::getenv("TARGET")) TARGET = std::atoi(e);
  {
    long long open = 0; int firstOpen = -1, heur = -1;
    for (int a = 0; a <= X; ++a) {
      const size_t sd = sideIndex(a, a);
      if (!notv[sd * GW + TARGET]) { ++open; if (firstOpen < 0) firstOpen = a; }
      if (gv[sd] == TARGET && heur < 0) heur = a;
    }
    std::printf("# target %d: G(w,w,a,a) != %d is proved for all a <= %d except %lld (first exception a = %d); first a with value %d if nothing dies later: %d\n",
                TARGET, TARGET, X, open, firstOpen, TARGET, heur);
  }

  std::vector<int> firstInf(GM + 2, -1), firstRect(GM + 2, -1), firstInfExact(GM + 2, -1);
  int diagExactUpTo = -1;                        // all a <= this have an exact diagonal value
  std::printf("# a  G(w,w,a,a)  G(a,a,a,a)   (above %d shown as -; ? = value not certified)\n", GM);
  for (int a = 0; a <= X; ++a) {
    const size_t sd = sideIndex(a, a);
    int gi = gv[sd], gr = -1;
    for (int g = 1; g <= GM; ++g) if (death[rowIndex(a, a, g)] == a) gr = g;
    if (a == 0) gr = 0;
    if (exact[sd] && diagExactUpTo == a - 1) diagExactUpTo = a;
    if (gi <= GM && firstInf[gi] < 0) firstInf[gi] = a;
    if (gi <= GM && exact[sd] && firstInfExact[gi] < 0) firstInfExact[gi] = a;
    if (gr >= 1 && firstRect[gr] < 0) firstRect[gr] = a;
    if (a <= 60 || gi <= GM) {
      std::printf("%d ", a);
      if (gi <= GM) std::printf("%d%s ", gi, exact[sd] ? "" : "?"); else std::printf("-%s ", exact[sd] ? "" : "?");
      if (gr >= 0) std::printf("%d\n", gr); else std::printf("-\n");
    }
  }
  std::printf("# value: first a with G(w,w,a,a) = value | first such a with a certified value | first a with G(a,a,a,a) = value\n");
  int mexL = 1, mexExact = 1;
  for (int g = 1; g <= GM; ++g) {
    std::printf("%d: %d | %d | %d\n", g, firstInf[g], firstInfExact[g], firstRect[g]);
    if (mexL == g && (firstInf[g] >= 0 || firstRect[g] >= 0)) ++mexL;
    if (mexExact == g && (firstInfExact[g] >= 0 || firstRect[g] >= 0)) ++mexExact;
  }
  std::printf("# least value not attained for a <= %d: %d%s; least value without a certified witness: %d\n",
              X, mexL, mexL > GM ? " (above GM)" : "", mexExact);
  long long nCertAlive = 0, nAlive = 0;
  for (size_t r = 0; r < nrow; ++r) if (!dead[r]) { ++nAlive; nCertAlive += cert[r]; }
  for (size_t k = 0; k < lags.size(); ++k)
    std::printf("# period %d certifies %lld rows alive at T\n", lags[k], certByLag[k]);
  std::printf("# certified: %lld of %lld rows alive at T; %lld of %zu sides have an exact value; diagonal exact for all a <= %d\n",
              nCertAlive, nAlive, nExact, nside, diagExactUpTo);

  // statistics on death levels
  long long alive = 0, still = 0, died = 0, late = 0;
  double maxRatio = 0; int mx = 0, my = 0, mg = 0, md = 0;
  int lastDeath = 0;
  for (int x = 0; x <= X; ++x)
    for (int y = 0; y <= x; ++y)
      for (int g = 1; g <= GM; ++g) {
        int d = death[rowIndex(x, y, g)];
        if (d == -1) { ++alive; continue; }
        if (d == -2) { ++still; continue; }
        ++died;
        lastDeath = std::max(lastDeath, d);
        if (d > T / 2) ++late;
        if (x >= 8) { double q = (double)d / x; if (q > maxRatio) { maxRatio = q; mx = x; my = y; mg = g; md = d; } }
      }
  std::printf("# rows: %lld died, %lld stillborn, %lld alive at T=%d; latest death at level %d; %lld deaths after T/2\n",
              died, still, alive, T, lastDeath, late);
  std::printf("# largest death level / x (x >= 8): %.3f at row (%d,%d,%d), level %d; largest offset used: %lld of %d; most rows living at once: %lld\n",
              maxRatio, mx, my, mg, md, overflowMax, NB, peakLive);
  if (argc > 5) {
    FILE* f = std::fopen(argv[5], "wb");
    if (f) { std::fwrite(death.data(), sizeof(int32_t), death.size(), f); std::fclose(f); }
  }
  if (const char* e = std::getenv("BIRTHS")) {     // the birth values A(x; x,y,g), in the same order
    FILE* f = std::fopen(e, "wb");
    if (f) { std::fwrite(birth.data(), sizeof(int32_t), birth.size(), f); std::fclose(f); }
  }
  return 0;
}
