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
//        rodf -K c -Z zmax [-v 1] -p ... COLS   decide every option "cut cell index c at height z"
//                                for z <= zmax (one process, shared memo); -v 1 prints each one.
//                                Stops at the first exact P (taller cuts have it as an option).
//                                -Y zmin starts the family at height zmin (to resume a run).
//        rodf -I 1 -p ... COLS   only decide, exactly, whether some cut of the poison column is P
//                                (position: poison and one other cell omega)
//        rodf -I 2 -p ... COLS   the same, but only the cuts above every finite height (a cut at
//                                height h <= H, H the largest finite height, is not considered)
//        rodf -I 2 -K c -Y zmin -Z zmax -p ... COLS   side set: the z for which the stalk left by
//                                cutting cell c at z has no P cut of the poison column above z;
//                                with -v 1 the other z are printed as [z:h], h the P height
//        rodf -S zsim ...        simulation limit for the two-wide-stalk certificate (default 30000)
//        rodf -M 0 ...           certify the whole closed family jointly, not member by member
//        rodf -L msim ...        step limit of one member's certificate (default 3000000); the
//                                joint certificate (limit -S) is only a fallback
//        rodf -P secs ...        progress report on stderr every secs seconds
//        rodf -F 0|1|2 ...       single-member certificates: 0 general simulation only, 1 bit-mask
//                                fast path (default), 2 both, aborting if they ever differ (test)
//        COLS = column heights of S, non-increasing, one digit each.
//        Prints whether S x omega is P or N and, for N, a winning move.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <pthread.h>
#include <string>

#include "rod.h"

using namespace rod;

static int ALPHA = 2, DSLACK = 6, ZSIM = 30000, MSIM = 3000000, PROGRESS = 0;
static bool PERMEMBER = true;
static int FASTMODE = 1;
static bool EXACT1 = true;
static int typeIOnly = 0;
static int familyCell = -1, familyMax = 0, familyMin = 0;
static bool familyVerbose = false;
static std::string cols, fquery, pquery, pquery0;
static int hmax = 0;

static void* run(void*) {
  RodSolver S(cols);
  S.ALPHA = ALPHA; S.DSLACK = DSLACK; S.EXACT1 = EXACT1; S.ZSIM = ZSIM; S.MSIM = MSIM; S.PERMEMBER = PERMEMBER; S.PROGRESS = PROGRESS;
  S.FASTCERT = FASTMODE >= 1; S.CHECKFAST = FASTMODE == 2;
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
    if (familyCell >= 0 && typeIOnly != 2) {  // decide every option "cut cell familyCell at height z", z = 0..familyMax
      int nP = 0, nNex = 0, nNh = 0, nPh = 0;
      for (int z = std::max(familyMin, familyCell == 0 ? 1 : 0); z <= familyMax; ++z) {
        if (h[familyCell] != OMEGA && z >= h[familyCell]) break;
        H g = S.cut(h, familyCell, z);
        uint8_t r = S.decide(g);
        bool P = r & 1, ex = r & 2;
        if (P) { if (ex) ++nP; else ++nPh; } else { if (ex) ++nNex; else ++nNh; }
        if (familyVerbose || P || !ex) {
          std::printf("  cut (%d,%d) at %d: %s%s", S.cx[familyCell], S.cy[familyCell], z, P ? "P" : "N", ex ? "" : "?");
          if (!P && familyVerbose) {
            Why w{-1, -1, false};
            if (g[0] == OMEGA) { bool anyW = false; for (int i = 1; i < NC; ++i) if (g[i] == OMEGA) anyW = true;
              if (anyW) { S.pw(g, &w); std::printf("   reply: cell (%d,%d) at %d", S.cx[w.cell], S.cy[w.cell], w.z); } }
          }
          std::printf("\n");
        }
        std::fflush(stdout);
        if (P && ex) {  // every taller cut has this one as an option, so it is N
          std::printf("  (cuts above %d are N: they have this P-position as an option)\n", z);
          break;
        }
      }
      std::printf("%s : family of cuts of cell (%d,%d), z <= %d: %d P exact, %d P heuristic, %d N exact, %d N heuristic\n",
                  pquery0.c_str(), S.cx[familyCell], S.cy[familyCell], familyMax, nP, nPh, nNex, nNh);
      return nullptr;
    }
    if (typeIOnly) {  // only the cuts of the poison column (two-wide stalk), certified
      int cW = -1, nW = 0;
      for (int i = 1; i < NC; ++i) if (h[i] == OMEGA) { ++nW; cW = i; }
      if (h[0] != OMEGA || nW != (familyCell >= 0 && typeIOnly == 2 ? 2 : 1)) { std::printf("%s : -I needs omega at the poison and one other cell\n", pquery0.c_str()); return nullptr; }
      if (typeIOnly == 2 && familyCell >= 0) {  // side set: the z in [zmin, zmax] for which
        // cutting familyCell at z leaves a stalk with no P cut of the poison column above z
        int cW2 = -1;
        for (int i = 1; i < NC; ++i) if (h[i] == OMEGA && i != familyCell) cW2 = i;
        std::printf("%s : side set of cell (%d,%d) in [%d,%d]:", pquery0.c_str(), S.cx[familyCell],
                    S.cy[familyCell], familyMin, familyMax);
        for (int z = familyMin; z <= familyMax; ++z) {
          H g = S.cut(h, familyCell, z);
          const RodSolver::Seq* sq = S.certify(g, cW2);
          if (!sq) { std::printf(" ?%d", z); std::fflush(stdout); continue; }
          bool p = false;
          int ph = -1;
          for (int y = z + 1; y < sq->start + (int)sq->off.size(); ++y) {
            int v = S.seqValue(*sq, g, cW2, y);
            if (v == y) { p = true; ph = y; break; }
            if (v < 0) break;
          }
          if (!p) { std::printf(" %d", z); std::fflush(stdout); }
          else if (familyVerbose) { std::printf(" [%d:%d]", z, ph); std::fflush(stdout); }
        }
        std::printf("\n");
        return nullptr;
      }
      if (typeIOnly == 2) {  // only the cuts above every finite height (the side-set test)
        int H0 = 0;
        for (int i = 1; i < NC; ++i) if (h[i] != OMEGA) H0 = std::max(H0, (int)h[i]);
        const RodSolver::Seq* sq = S.certify(h, cW);
        if (!sq) { std::printf("%s : cuts above %d UNDECIDED\n", pquery0.c_str(), H0); return nullptr; }
        int found = -1;
        for (int z = H0 + 1; z < sq->start + (int)sq->off.size(); ++z) {
          int v = S.seqValue(*sq, h, cW, z);
          if (v == z) { found = z; break; }
          if (v < 0) break;
        }
        if (found >= 0) std::printf("%s : cuts above %d: P at height %d\n", pquery0.c_str(), H0, found);
        else std::printf("%s : cuts above %d: no P-position\n", pquery0.c_str(), H0);
        return nullptr;
      }
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
    std::fprintf(stderr, "[%lld f-values, %lld omega-positions; two-wide stalks: %lld certified, %lld not; "
                 "sequence cache: %lld stored, %lld hits; members certified alone: %lld, failed %lld; "
                 "fast path: %lld overflows, %lld checked]\n",
                 S.fcount, S.wcount, S.typeICertified, S.typeIUncertified, S.seqStored, S.seqHits,
                 S.memberCertified, S.memberFailed, S.fastOverflow, S.fastChecked);
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
    else if (!std::strcmp(argv[i], "-I")) typeIOnly = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-K")) familyCell = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-Z")) familyMax = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-Y")) familyMin = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-v")) familyVerbose = std::atoi(argv[i + 1]) != 0;
    else if (!std::strcmp(argv[i], "-S")) ZSIM = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-M")) PERMEMBER = std::atoi(argv[i + 1]) != 0;
    else if (!std::strcmp(argv[i], "-L")) MSIM = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-P")) PROGRESS = std::atoi(argv[i + 1]);
    else if (!std::strcmp(argv[i], "-F")) FASTMODE = std::atoi(argv[i + 1]);
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
