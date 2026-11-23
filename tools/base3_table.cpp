// Dense exact table of finite Chomp positions over the 3x3 base.
//
// A position is a plane partition a(x,y), 0 <= x,y <= 2 (heights, weakly decreasing in x and
// in y), with the poison at (0,0,0). A bite at (x,y,t) cuts every cell (x',y') with x' >= x,
// y' >= y down to height t. The player who takes the poison loses.
//
// For a "rest" r (the heights of the eight cells other than (0,0)) at most one height a of
// the poison column makes [a; r] a P-position, because lowering that column is a move. The
// table stores this partner pi(r), for every rest within the given caps:
//   * r is "killed" if some a' with 1 <= a' < m = max(r) has pi(min(r, a')) = a'. Then no
//     [a; r] is P.
//   * otherwise pi(r) is the least a >= max(m, 1) that is not pi(r') for a rest r' obtained
//     from r by one bite at a cell other than (0,0).
// Values above H are not needed and are stored as "none".
//
// Layout. Cells: column 1 = (1,0),(1,1),(1,2) = u >= v >= w; column 0 = (0,1),(0,2) = p >= q
// with p >= v, q >= w; column 2 = (2,0),(2,1),(2,2) = d >= e >= f with d <= u, e <= v,
// f <= w. The rests with the same (u,v,w,p,q) form a block, stored contiguously. A bite
// outside column 2 maps a block into one other block, so its values are read as a stream.
// Blocks with the same u+v+w+p+q do not depend on each other and are done in parallel.
//
// usage: base3_table H [-c caps] [-q queryfile] [-s] [-t] [-P dumpfile]
//   caps: nine entries for (0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2); the first
//         is ignored; "H" or a number. Default: all H. Caps are made monotone.
//   -s    P-heights of all Young diagrams inside the set of cells with cap H
//   -t    for the base of all cells with cap H: the finite P cuts of its towers T(b,g)
//   -q    queries, one per line: nine entries in the same order, each a number, "h", "h+K"
//         or "h-K". Prints the h for which the position is P, as ranges, among the h for
//         which it is a plane partition inside the table.
//         A line "m" followed by nine numbers lists the winning bites of that position.
//   -F    scan for positions all of whose infinite cuts have finite replies. The cells with
//         cap H are taken as infinite, the others carry an attachment. For every attachment
//         within the caps: is some cut of the poison column P (then the position is N), and
//         for each infinite cell c and height z, does cutting c at z leave a position with a
//         P cut of the poison column? Prints the attachments with no P cut and with every
//         z from ZLOW (default 4) to H/2 answered in this way. With VERBOSE=1 every
//         attachment without a P cut is listed, with the unanswered heights per cell.
//   -P    write all P-positions [a; r] with a <= H (for checks at small H)
//
// environment: DRY=1 prints the table size and stops; PROGRESS=1 reports levels on stderr.
//
// build: g++ -O3 -march=native -std=c++17 -Wall -fopenmp -o base3_table tools/base3_table.cpp
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <vector>
#include <omp.h>

typedef uint64_t u64;
typedef uint32_t u32;
typedef uint8_t u8;

static int H;
static int Cu, Cv, Cw, Cp, Cq, Cd, Ce, Cf;
static std::vector<u32> B1, B2;
static std::vector<u64> off;
static std::vector<std::vector<u64>> F0;  // F0[w][a]
static std::vector<std::vector<u32>> K1;  // K1[w][b]
static std::vector<u32> K2;               // K2[(v*(Cw+1)+w)*(H+2)+a]
static u8* tab;
static int W;  // bitset words

static inline u32 id1(int u, int v, int w) { return B1[u] + B2[v] + (u32)w; }
static inline const u32* K2row(int v, int w) {
  return &K2[((size_t)v * (Cw + 1) + w) * (H + 2)];
}
static inline u64 index_of(int u, int v, int w, int p, int q, int d, int e, int f) {
  const u32* k2 = K2row(v, w);
  u64 n2 = k2[std::min(u, Cd) + 1];
  return off[id1(u, v, w)] + (F0[w][p] - F0[w][v] + (u64)(q - w)) * n2 + k2[d] + K1[w][e] + f;
}

struct Scratch {
  std::vector<u64> ex, accD, accE;
  std::vector<u8> killed;
};

static void process(int u, int v, int w, int p, int q, Scratch& sc) {
  const int m = std::max(u, p);
  const int dmax = std::min(u, Cd);
  const int ecap = std::min(v, Ce), fcap = std::min(w, Cf);
  const u32* k2 = K2row(v, w);
  const u64 n2 = k2[dmax + 1];
  u8* blk = tab + off[id1(u, v, w)] + (F0[w][p] - F0[w][v] + (u64)(q - w)) * n2;
  if (m == 0) {
    blk[0] = 1;
    return;
  }
  if (sc.ex.size() < n2 * W) sc.ex.resize(n2 * W);
  if (sc.killed.size() < n2) sc.killed.resize(n2);
  u64* ex = sc.ex.data();
  u8* killed = sc.killed.data();
  memset(ex, 0, n2 * W * sizeof(u64));
  memset(killed, 0, n2);
  const unsigned span = (unsigned)(H - m);
  const int INF = 1 << 20;

  auto stream = [&](int u2, int v2, int w2, int p2, int q2, int td, int te, int tf, int killA) {
    const u32* k2t = K2row(v2, w2);
    const u32* k1t = K1[w2].data();
    const u64 n2t = k2t[std::min(u2, Cd) + 1];
    const u8* tb = tab + off[id1(u2, v2, w2)] + (F0[w2][p2] - F0[w2][v2] + (u64)(q2 - w2)) * n2t;
    size_t i = 0;
    for (int d = 0; d <= dmax; ++d) {
      const u8* bd = tb + k2t[std::min(d, td)];
      const int emax = std::min(d, ecap);
      for (int e = 0; e <= emax; ++e) {
        const u8* be = bd + k1t[std::min(e, te)];
        const int fmax = std::min(e, fcap);
        if (killA < 0) {
          for (int f = 0; f <= fmax; ++f, ++i) {
            unsigned o = (unsigned)be[std::min(f, tf)] - (unsigned)m;
            if (o <= span) ex[i * W + (o >> 6)] |= 1ull << (o & 63);
          }
        } else {
          for (int f = 0; f <= fmax; ++f, ++i)
            if (be[std::min(f, tf)] == killA) killed[i] = 1;
        }
      }
    }
  };
  for (int t = 0; t < u; ++t) stream(t, std::min(v, t), std::min(w, t), p, q, t, t, t, -1);
  for (int t = 0; t < v; ++t) stream(u, t, std::min(w, t), p, q, INF, t, t, -1);
  for (int t = 0; t < w; ++t) stream(u, v, t, p, q, INF, INF, t, -1);
  for (int t = 0; t < p; ++t)
    stream(u, std::min(v, t), std::min(w, t), t, std::min(q, t), INF, t, t, -1);
  for (int t = 0; t < q; ++t) stream(u, v, std::min(w, t), p, t, INF, INF, t, -1);
  for (int a = 1; a < m; ++a)
    stream(std::min(u, a), std::min(v, a), std::min(w, a), std::min(p, a), std::min(q, a), a, a,
           a, a);

  // Bites inside column 2, by accumulators along d, e and f.
  const int FW = fcap + 1;
  if (sc.accD.size() < (size_t)(ecap + 1) * FW * W) sc.accD.resize((size_t)(ecap + 1) * FW * W);
  if (sc.accE.size() < (size_t)FW * W) sc.accE.resize((size_t)FW * W);
  u64* accD = sc.accD.data();
  u64* accE = sc.accE.data();
  u64 runF[4], bits[4];
  for (int k = 0; k < W; ++k) accD[k] = 0;
  size_t i = 0;
  for (int d = 0; d <= dmax; ++d) {
    const int emax = std::min(d, ecap);
    if (d > 0 && emax == d) {
      const int fm = std::min(d, fcap);
      for (int f = 0; f <= fm; ++f)
        for (int k = 0; k < W; ++k)
          accD[((size_t)d * FW + f) * W + k] = accD[((size_t)(d - 1) * FW + std::min(f, d - 1)) * W + k];
    }
    for (int k = 0; k < W; ++k) accE[k] = 0;
    for (int e = 0; e <= emax; ++e) {
      const int fmax = std::min(e, fcap);
      if (e > 0 && fmax == e)
        for (int k = 0; k < W; ++k) accE[(size_t)e * W + k] = accE[(size_t)(e - 1) * W + k];
      for (int k = 0; k < W; ++k) runF[k] = 0;
      for (int f = 0; f <= fmax; ++f, ++i) {
        u64* aD = &accD[((size_t)e * FW + f) * W];
        u64* aE = &accE[(size_t)f * W];
        u8 val = 255;
        if (!killed[i]) {
          for (int k = 0; k < W; ++k) bits[k] = ex[i * W + k] | runF[k] | aE[k] | aD[k];
          for (int k = 0; k < W; ++k)
            if (~bits[k]) {
              unsigned o = (unsigned)k * 64 + (unsigned)__builtin_ctzll(~bits[k]);
              if (o <= span) {
                val = (u8)(m + o);
                const u64 b = 1ull << (o & 63);
                runF[k] |= b;
                aE[k] |= b;
                aD[k] |= b;
              }
              break;
            }
        }
        blk[i] = val;
      }
    }
  }
}

// ---- queries -----------------------------------------------------------------------------
// a[x][y], x-major. Returns 1 if P, 0 if N, -1 if not a plane partition or outside the caps.
static int is_P(const int a[3][3]) {
  for (int x = 0; x < 3; ++x)
    for (int y = 0; y < 3; ++y) {
      if (x + 1 < 3 && a[x + 1][y] > a[x][y]) return -1;
      if (y + 1 < 3 && a[x][y + 1] > a[x][y]) return -1;
    }
  const int u = a[1][0], v = a[1][1], w = a[1][2], p = a[0][1], q = a[0][2];
  const int d = a[2][0], e = a[2][1], f = a[2][2];
  if (u > Cu || v > Cv || w > Cw || p > Cp || q > Cq || d > Cd || e > Ce || f > Cf) return -1;
  if (a[0][0] < 1 || a[0][0] > H) return -1;
  return tab[index_of(u, v, w, p, q, d, e, f)] == a[0][0];
}

int main(int argc, char** argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: base3_table H [-c caps] [-q queryfile] [-s] [-t] [-P dumpfile]\n");
    return 1;
  }
  H = atoi(argv[1]);
  if (H < 1 || H > 254) {
    fprintf(stderr, "need 1 <= H <= 254\n");
    return 1;
  }
  int cap[3][3];
  for (auto& row : cap)
    for (int& c : row) c = H;
  const char* qfile = nullptr;
  const char* pfile = nullptr;
  bool doS = false, doT = false, doF = false;
  for (int i = 2; i < argc; ++i) {
    std::string s = argv[i];
    if (s == "-c" && i + 1 < argc) {
      char* str = argv[++i];
      int k = 0;
      for (char* tok = strtok(str, ", "); tok && k < 9; tok = strtok(nullptr, ", "), ++k)
        cap[k / 3][k % 3] = (tok[0] == 'H' || tok[0] == 'h') ? H : std::min(H, atoi(tok));
      if (k != 9) {
        fprintf(stderr, "caps: need nine entries\n");
        return 1;
      }
    } else if (s == "-q" && i + 1 < argc) {
      qfile = argv[++i];
    } else if (s == "-P" && i + 1 < argc) {
      pfile = argv[++i];
    } else if (s == "-s") {
      doS = true;
    } else if (s == "-t") {
      doT = true;
    } else if (s == "-F") {
      doF = true;
    } else {
      fprintf(stderr, "unknown argument %s\n", argv[i]);
      return 1;
    }
  }
  cap[0][0] = H;
  for (int x = 0; x < 3; ++x)
    for (int y = 0; y < 3; ++y) {
      if (x > 0) cap[x][y] = std::min(cap[x][y], cap[x - 1][y]);
      if (y > 0) cap[x][y] = std::min(cap[x][y], cap[x][y - 1]);
    }
  Cu = cap[1][0], Cv = cap[1][1], Cw = cap[1][2], Cp = cap[0][1], Cq = cap[0][2];
  Cd = cap[2][0], Ce = cap[2][1], Cf = cap[2][2];
  W = (H + 64) / 64;

  B2.assign(Cv + 2, 0);
  for (int b = 0; b <= Cv; ++b) B2[b + 1] = B2[b] + std::min(b, Cw) + 1;
  B1.assign(Cu + 2, 0);
  for (int a = 0; a <= Cu; ++a) B1[a + 1] = B1[a] + B2[std::min(a, Cv) + 1];
  F0.assign(Cw + 1, std::vector<u64>(Cp + 2, 0));
  for (int w = 0; w <= Cw; ++w)
    for (int a = w; a <= Cp; ++a) F0[w][a + 1] = F0[w][a] + (std::min(a, Cq) - w + 1);
  K1.assign(Cw + 1, std::vector<u32>(H + 2, 0));
  for (int w = 0; w <= Cw; ++w)
    for (int b = 0; b <= H; ++b) K1[w][b + 1] = K1[w][b] + std::min(b, std::min(w, Cf)) + 1;
  K2.assign((size_t)(Cv + 1) * (Cw + 1) * (H + 2), 0);
  for (int v = 0; v <= Cv; ++v)
    for (int w = 0; w <= std::min(v, Cw); ++w) {
      u32* k2 = &K2[((size_t)v * (Cw + 1) + w) * (H + 2)];
      for (int a = 0; a <= H; ++a) k2[a + 1] = k2[a] + K1[w][std::min(a, std::min(v, Ce)) + 1];
    }
  off.assign(B1[Cu + 1] + 1, 0);
  u64 N = 0;
  for (int u = 0; u <= Cu; ++u)
    for (int v = 0; v <= std::min(u, Cv); ++v)
      for (int w = 0; w <= std::min(v, Cw); ++w) {
        off[id1(u, v, w)] = N;
        N += (F0[w][Cp + 1] - F0[w][v]) * (u64)K2row(v, w)[std::min(u, Cd) + 1];
      }
  printf("H = %d, caps (0,1),(0,2) = %d,%d; (1,0),(1,1),(1,2) = %d,%d,%d; (2,0),(2,1),(2,2) = %d,%d,%d\n",
         H, Cp, Cq, Cu, Cv, Cw, Cd, Ce, Cf);
  printf("rests: %llu (%.2f GB), threads: %d\n", (unsigned long long)N, N / 1073741824.0,
         omp_get_max_threads());
  fflush(stdout);
  if (getenv("DRY")) return 0;  // sizes only
  tab = (u8*)malloc(N);
  if (!tab) {
    fprintf(stderr, "out of memory\n");
    return 1;
  }

  const double t0 = omp_get_wtime();
  const int Smax = Cu + Cv + Cw + Cp + Cq;
  const bool progress = getenv("PROGRESS") != nullptr;
#pragma omp parallel
  {
    Scratch sc;
    for (int s = 0; s <= Smax; ++s) {
#pragma omp for collapse(2) schedule(dynamic, 1)
      for (int u = 0; u <= Cu; ++u)
        for (int v = 0; v <= Cv; ++v) {
          if (v > u) continue;
          for (int w = 0; w <= std::min(v, Cw); ++w) {
            const int R = s - u - v - w;
            if (R < 0) break;
            for (int p = std::max(v, (R + 1) / 2); p <= std::min(Cp, R - w); ++p) {
              const int q = R - p;
              if (q > Cq) continue;
              process(u, v, w, p, q, sc);
            }
          }
        }
#pragma omp single
      if (progress && s % 8 == 0) {
        fprintf(stderr, "level %d / %d, %.0f s\n", s, Smax, omp_get_wtime() - t0);
      }
    }
  }
  printf("table built in %.1f s\n", omp_get_wtime() - t0);
  fflush(stdout);

  // the base of free cells
  bool freeCell[3][3];
  for (int x = 0; x < 3; ++x)
    for (int y = 0; y < 3; ++y) freeCell[x][y] = cap[x][y] == H;
  int col[3];  // column heights of the free base
  for (int x = 0; x < 3; ++x) {
    col[x] = 0;
    while (col[x] < 3 && freeCell[x][col[x]]) ++col[x];
  }

  if (doS) {
    printf("\nP-heights of the Young diagrams inside the free base %d%d%d (column heights):\n",
           col[0], col[1], col[2]);
    for (int c0 = 1; c0 <= col[0]; ++c0)
      for (int c1 = 0; c1 <= std::min(c0, col[1]); ++c1)
        for (int c2 = 0; c2 <= std::min(c1, col[2]); ++c2) {
          const int cc[3] = {c0, c1, c2};
          int found = 0;
          for (int h = 1; h <= H && !found; ++h) {
            int a[3][3];
            for (int x = 0; x < 3; ++x)
              for (int y = 0; y < 3; ++y) a[x][y] = y < cc[x] ? h : 0;
            if (is_P(a) == 1) found = h;
          }
          if (found)
            printf("  %d%d%d : h = %d\n", c0, c1, c2, found);
          else
            printf("  %d%d%d : h > %d\n", c0, c1, c2, H);
        }
  }
  if (doT) {
    printf("\nFinite P cuts of the towers of the base %d%d%d: cells above b at height g, the rest at h.\n",
           col[0], col[1], col[2]);
    for (int bx = 0; bx < 3; ++bx)
      for (int by = 0; by < 3; ++by) {
        if ((bx == 0 && by == 0) || !freeCell[bx][by]) continue;
        printf("  b = (%d,%d):", bx, by);
        std::vector<int> un;
        for (int g = 0; g < H; ++g) {
          int found = 0;
          for (int h = g + 1; h <= H && !found; ++h) {
            int a[3][3];
            for (int x = 0; x < 3; ++x)
              for (int y = 0; y < 3; ++y)
                a[x][y] = !freeCell[x][y] ? 0 : (x >= bx && y >= by) ? g : h;
            if (is_P(a) == 1) found = h;
          }
          if (found)
            printf(" %d->%d", g, found);
          else
            un.push_back(g);
        }
        printf("\n    no cut up to %d for g =", H);
        for (int g : un) printf(" %d", g);
        printf("\n");
      }
  }
  if (doF) {
    const int ZLOW = getenv("ZLOW") ? atoi(getenv("ZLOW")) : 4;
    const int ZTOP = H / 2;
    const bool verbose = getenv("VERBOSE") != nullptr;
    int att[3][3];
    std::vector<std::pair<int, int>> ac;  // attachment cells
    for (int x = 0; x < 3; ++x)
      for (int y = 0; y < 3; ++y)
        if (!freeCell[x][y]) ac.push_back({x, y});
    long long total = 0, nocut = 0, cand = 0;
    printf("\nPositions with the cells of cap %d infinite (w) and every infinite cut answered by a finite reply,\n"
           "for cut heights %d..%d. Order (0,0),(0,1),(0,2) | (1,0),... ; in brackets: lower cuts without a finite reply.\n",
           H, ZLOW, ZTOP);
    std::vector<int> v(ac.size(), 0);
    while (true) {
      for (size_t i = 0; i < ac.size(); ++i) att[ac[i].first][ac[i].second] = v[i];
      bool valid = true;
      for (size_t i = 0; i < ac.size() && valid; ++i) {
        const int x = ac[i].first, y = ac[i].second;
        if (x > 0 && !freeCell[x - 1][y] && att[x - 1][y] < v[i]) valid = false;
        if (y > 0 && !freeCell[x][y - 1] && att[x][y - 1] < v[i]) valid = false;
      }
      if (valid) {
        ++total;
        int amax = 0;
        for (int vi : v) amax = std::max(amax, vi);
        auto build = [&](int a[3][3], int h, int cx, int cy, int z) {
          for (int x = 0; x < 3; ++x)
            for (int y = 0; y < 3; ++y) {
              int val = freeCell[x][y] ? h : att[x][y];
              if (cx >= 0 && x >= cx && y >= cy) val = std::min(val, z);
              a[x][y] = val;
            }
        };
        int a[3][3], cut = 0;
        for (int h = std::max(1, amax); h <= H && !cut; ++h) {
          build(a, h, -1, -1, 0);
          if (is_P(a) == 1) cut = h;
        }
        if (!cut) {
          ++nocut;
          bool ok = true;
          std::string low, high;
          for (int cx = 0; cx < 3 && (ok || verbose); ++cx)
            for (int cy = 0; cy < 3 && (ok || verbose); ++cy) {
              if ((cx == 0 && cy == 0) || !freeCell[cx][cy]) continue;
              std::string un;
              for (int z = 0; z <= ZTOP && (ok || verbose); ++z) {
                bool found = false;
                for (int h = z + 1; h <= H && !found; ++h) {
                  build(a, h, cx, cy, z);
                  if (is_P(a) == 1) found = true;
                }
                if (!found) {
                  if (z >= ZLOW) { ok = false; un += " " + std::to_string(z); }
                  else low += " (" + std::to_string(cx) + "," + std::to_string(cy) + ")@" + std::to_string(z);
                }
              }
              if (!un.empty()) high += " (" + std::to_string(cx) + "," + std::to_string(cy) + "):" + un + ";";
            }
          if (!ok && verbose) low += " | unanswered" + high;
          if (ok || verbose) {
            ++cand;
            printf(" ");
            for (int x = 0; x < 3; ++x) {
              for (int y = 0; y < 3; ++y) {
                if (freeCell[x][y]) printf(" w"); else printf(" %d", att[x][y]);
              }
              if (x < 2) printf(" |");
            }
            printf("   [%s ]\n", low.c_str());
          }
        }
      }
      size_t i = 0;
      while (i < ac.size()) {
        if (++v[i] <= cap[ac[i].first][ac[i].second]) break;
        v[i++] = 0;
      }
      if (i == ac.size()) break;
    }
    printf("attachments: %lld; without a P cut of the poison column up to %d: %lld; listed: %lld\n",
           total, H, nocut, cand);
  }
  if (qfile) {
    FILE* fq = fopen(qfile, "r");
    if (!fq) {
      fprintf(stderr, "cannot open %s\n", qfile);
      return 1;
    }
    char line[512];
    printf("\nQueries (order (0,0),(0,1),(0,2),(1,0),...):\n");
    while (fgets(line, sizeof line, fq)) {
      if (line[0] == '#' || line[0] == '\n') continue;
      if (line[0] == 'm') {
        int a[3][3], k = 0;
        char copy[512];
        strcpy(copy, line + 1);
        for (char* tok = strtok(copy, ", \t\n"); tok && k < 9; tok = strtok(nullptr, ", \t\n"), ++k)
          a[k / 3][k % 3] = atoi(tok);
        if (k != 9) continue;
        line[strcspn(line, "\n")] = 0;
        int r = is_P(a);
        printf("  %s : %s", line, r < 0 ? "outside the table" : r ? "P" : "N, winning bites (x,y)@t:");
        if (r == 0)
          for (int x = 0; x < 3; ++x)
            for (int y = 0; y < 3; ++y)
              for (int t = (x == 0 && y == 0) ? 1 : 0; t < a[x][y]; ++t) {
                int b[3][3];
                for (int i2 = 0; i2 < 3; ++i2)
                  for (int j2 = 0; j2 < 3; ++j2)
                    b[i2][j2] = (i2 >= x && j2 >= y) ? std::min(a[i2][j2], t) : a[i2][j2];
                if (is_P(b) == 1) printf(" (%d,%d)@%d", x, y, t);
              }
        printf("\n");
        continue;
      }
      int val[9], isH[9], k = 0;
      char copy[512];
      strcpy(copy, line);
      for (char* tok = strtok(copy, ", \t\n"); tok && k < 9; tok = strtok(nullptr, ", \t\n"), ++k) {
        isH[k] = tok[0] == 'h' || tok[0] == 'H';
        val[k] = isH[k] ? atoi(tok + 1) : atoi(tok);  // "h+3" -> 3, "h-2" -> -2, "h" -> 0
      }
      if (k != 9) continue;
      line[strcspn(line, "\n")] = 0;
      printf("  %s :", line);
      int nP = 0, nN = 0, runStart = -1, hlo = -1, hhi = -1;
      for (int h = 0; h <= H + 1; ++h) {
        int a[3][3];
        for (int j = 0; j < 9; ++j) a[j / 3][j % 3] = isH[j] ? h + val[j] : val[j];
        bool neg = false;
        for (int j = 0; j < 9; ++j) neg |= a[j / 3][j % 3] < 0;
        const int r = (neg || h > H) ? -1 : is_P(a);
        if (r >= 0) {
          if (hlo < 0) hlo = h;
          hhi = h;
          if (r) ++nP; else ++nN;
        }
        if (r == 1 && runStart < 0) runStart = h;
        if (r != 1 && runStart >= 0) {
          if (runStart == h - 1) printf(" P at h = %d;", runStart);
          else printf(" P for h = %d..%d;", runStart, h - 1);
          runStart = -1;
        }
      }
      printf(" %d P, %d N among h = %d..%d\n", nP, nN, hlo, hhi);
    }
    fclose(fq);
  }
  if (pfile) {
    FILE* fp = fopen(pfile, "w");
    for (int u = 0; u <= Cu; ++u)
      for (int v = 0; v <= std::min(u, Cv); ++v)
        for (int w = 0; w <= std::min(v, Cw); ++w)
          for (int p = v; p <= Cp; ++p)
            for (int q = w; q <= std::min(p, Cq); ++q)
              for (int d = 0; d <= std::min(u, Cd); ++d)
                for (int e = 0; e <= std::min(d, std::min(v, Ce)); ++e)
                  for (int f = 0; f <= std::min(e, std::min(w, Cf)); ++f) {
                    int a = tab[index_of(u, v, w, p, q, d, e, f)];
                    if (a != 255)
                      fprintf(fp, "%d %d %d %d %d %d %d %d %d\n", a, p, q, u, v, w, d, e, f);
                  }
    fclose(fp);
  }
  return 0;
}
