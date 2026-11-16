// Fast solver for Chomp on S x omega, where S is a finite Young diagram (cross-section) and
// the third axis is infinite. Uses the classic "completing height" reduction.
//
// A position is a height h(c) in N or omega for each cell c of S, non-increasing in x and y.
// Cell 0 = (0,0) is the poison column. Call the heights of the other cells the "rest".
//
// Finite rests. Fix a finite rest r with maximum m. Among the positions (a, r) with
// a >= max(1, m), exactly one or none is P (each is an option of every taller one). Call its
// height f(r), or NONE. Then
//   * f(r) = NONE if some move on the poison column below m wins, i.e. f(min(r, z)) = z for some
//     1 <= z < m (that child (z, min(r,z)) is P for every a, so every (a, r) is N);
//   * otherwise f(r) = least a >= max(1, m) not in E(r) = { f(r') : r' a move on the rest }.
// All f values are exact.
//
// Rests with omega. (omega, r) with r finite is always N (cut the poison column at f(r), or
// use the killing move). For r with omega cells, (omega, r) is P iff no option is P:
//   (1) cuts of the poison column at z >= 1: child (z, min(r, z)) is P iff f(min(r,z)) = z;
//   (2) moves on the rest leaving an omega cell: child (omega, r') is P iff Pw(r').
// Moves at height z inside an omega column are infinitely many; only z <= ALPHA*H + D is tried,
// where H is the largest finite height in the position. So Pw results are HEURISTIC unless
// marked exact: N is exact when witnessed by a finite P child.
//
// The solver itself is in rod.h (shared with chomp3p.cpp); this file is the command-line tool.
//
// Usage: rodf [-a ALPHA] [-d D] COLS          e.g. rodf 333 (3x3 base), rodf 21 (3-cell L)
//        rodf -H T COLS     exact: least t <= T with S x t a P-position (the finite P-height)
//        rodf -f r1,r2,.. COLS   exact: f(rest) for a finite rest (debugging)
//        rodf -p h0,h1,.. COLS   decide one position; heights of all cells in order (poison
//                                first, cells listed column by column), 'w' = omega
//        rodf -x 0 ...           disable the exact two-wide-stalk analysis (heuristic caps only)
//        rodf -I 1 -p ... COLS   only decide, exactly, whether some cut of the poison column is P
//                                (position: poison and one other cell omega)
//        COLS = column heights of S, non-increasing, one digit each.
//        Prints whether S x omega is P or N and, for N, a winning move.
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <string>

#include "rod.h"

using namespace rod;

static int ALPHA = 2, DSLACK = 6;
static bool EXACT1 = true;
static bool typeIOnly = false;
static std::string cols, fquery, pquery, pquery0;
static int hmax = 0;

static void* run(void*) {
  RodSolver S(cols);
  S.ALPHA = ALPHA; S.DSLACK = DSLACK; S.EXACT1 = EXACT1;
  int NC = S.NC;
  if (NC > 16) { std::fprintf(stderr, "at most 16 cells\n"); std::exit(1); }
  if (hmax > 0) {  // finite P-height: least t <= hmax with S x t a P-position (unique if any)
    for (int t = 1; t <= hmax; ++t) {
      H h(NC, (uint8_t)t);
      if (NC == 1 ? t == 1 : S.f(h) == t) {
        std::printf("%s : h = %d   [%lld f-values]\n", cols.c_str(), t, S.fcount);
        return nullptr;
      }
    }
    std::printf("%s : h > %d   [%lld f-values]\n", cols.c_str(), hmax, S.fcount);
    return nullptr;
  }
  if (!pquery.empty()) {  // decide one position: heights of all cells (poison first), 'w' = omega
    H h(NC, 0);
    int idx2 = 0;
    for (char* tok = std::strtok(&pquery[0], ","); tok && idx2 < NC; tok = std::strtok(nullptr, ","))
      h[idx2++] = (tok[0] == 'w') ? OMEGA : (uint8_t)std::atoi(tok);
    bool anyW = false;
    for (int i = 1; i < NC; ++i) if (h[i] == OMEGA) anyW = true;
    if (typeIOnly) {  // only the cuts of the poison column (two-wide stalk), certified
      int cW = -1, nW = 0;
      for (int i = 1; i < NC; ++i) if (h[i] == OMEGA) { ++nW; cW = i; }
      if (h[0] != OMEGA || nW != 1) { std::printf("%s : -I needs omega at the poison and one other cell\n", pquery0.c_str()); return nullptr; }
      TypeIResult t = S.typeI(h, cW);
      std::printf("%s : poison cuts %s%s", pquery0.c_str(), t.decided ? "decided" : "UNDECIDED",
                  t.decided ? (t.hasP ? ", P at height " : ", no P-position") : "");
      if (t.decided && t.hasP) std::printf("%d", t.z);
      std::printf("   [period %d, %d states]\n", t.period, t.states);
      return nullptr;
    }
    if (h[0] != OMEGA) {
      uint16_t v = S.f(h);
      std::printf("%s : %s exact (finite)\n", pquery0.c_str(), (v == h[0]) ? "P" : "N");
    } else if (!anyW) {
      std::printf("%s : N exact (one infinite column)\n", pquery0.c_str());
    } else {
      Why w{-1, -1, false};
      uint8_t r = S.pw(h, &w);
      std::printf("%s : %s %s", pquery0.c_str(), (r & 1) ? "P" : "N", (r & 2) ? "exact" : "heuristic");
      if (!(r & 1)) std::printf("   move: cell (%d,%d) at height %d", S.cx[w.cell], S.cy[w.cell], w.z);
      std::printf("\n");
    }
    return nullptr;
  }
  if (!fquery.empty()) {  // debug: print f(rest) for a finite rest given as comma list
    H h(NC, 0);
    int idx = 1;
    for (char* tok = std::strtok(&fquery[0], ","); tok && idx < NC; tok = std::strtok(nullptr, ","))
      h[idx++] = std::atoi(tok);
    uint16_t v = S.f(h);
    if (v == NONE) std::printf("f = NONE\n"); else std::printf("f = %d\n", v);
    return nullptr;
  }
  H h(NC, OMEGA);
  if (NC == 1) { std::printf("%s x omega : N exact (heap omega)\n", cols.c_str()); return nullptr; }
  Why w{-1, -1, false};
  uint8_t r = S.pw(h, &w);
  std::printf("%s x omega : %s %s", cols.c_str(), (r & 1) ? "P" : "N", (r & 2) ? "exact" : "heuristic");
  if (!(r & 1)) std::printf("   winning move: cell (%d,%d) at height %d%s", S.cx[w.cell], S.cy[w.cell], w.z,
                            w.exact ? "" : " (child P heuristic)");
  std::printf("   [a=%d d=%d; %lld f-values, %lld omega-positions; two-wide stalks: %lld certified, %lld not]\n",
              ALPHA, DSLACK, S.fcount, S.wcount, S.typeICertified, S.typeIUncertified);
  return nullptr;
}

int main(int argc, char** argv) {
  int i = 1;
  while (i + 1 < argc && argv[i][0] == '-') {
    if (!std::strcmp(argv[i], "-a")) ALPHA = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-d")) DSLACK = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-f")) fquery = argv[i + 1];
    else if (!std::strcmp(argv[i], "-p")) { pquery = argv[i + 1]; pquery0 = argv[i + 1]; }
    else if (!std::strcmp(argv[i], "-H")) hmax = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-x")) EXACT1 = std::atoi(argv[i + 1]) != 0;
    else if (!std::strcmp(argv[i], "-I")) typeIOnly = std::atoi(argv[i + 1]) != 0;
    i += 2;
  }
  if (i >= argc) { std::fprintf(stderr, "usage: rodf [-a A] [-d D] COLS\n"); return 1; }
  cols = argv[i];
  pthread_attr_t attr;
  pthread_attr_init(&attr);
  pthread_attr_setstacksize(&attr, (size_t)2 << 30);
  pthread_t th;
  pthread_create(&th, &attr, run, nullptr);
  pthread_join(th, nullptr);
  return 0;
}
