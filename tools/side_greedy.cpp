// usage: side_greedy N [1]   (checks the greedy-matching description of the diagonal; 1: print rows h <= 60)
// Diagnostics for the greedy-matching view of the 2D side class.
// Computes the full table A(b,c) (unique a with [a,b,c] P, or -1) for b <= N, then for each row
// h checks: matched column of h == least column c < h that is unmatched before h and not blocked
// by a P-position [h,b',c''] with b' < h (point block if c'' < b', half-line c >= b' if c'' = b').
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
int main(int argc, char** argv) {
  int N = atoi(argv[1]);
  int mode = argc > 2 ? atoi(argv[2]) : 0;
  std::vector<std::vector<int>> A(N + 1);
  std::vector<int> tau(N + 1, -1);
  // straightforward O(N^3)-ish computation with stamps (fine for N <= 4000)
  int V = 4 * N + 10;
  std::vector<int> mark(V, 0); int stamp = 0;
  for (int b = 0; b <= N; ++b) A[b].assign(b + 1, -2);
  for (int c = 0; c <= N; ++c) {
    for (int b = c; b <= N; ++b) {
      if (tau[c] >= 0 && tau[c] < b) { A[b][c] = -1; continue; }
      ++stamp;
      for (int c2 = 0; c2 < c; ++c2) { int v = A[b][c2]; if (v >= 0) mark[v] = stamp; }
      for (int j = c; j < b; ++j) { int v = A[j][c]; if (v >= 0) mark[v] = stamp; }
      for (int j = 0; j < c; ++j) { int v = A[j][j]; if (v >= 0) mark[v] = stamp; }
      int a = b < 1 ? 1 : b;
      while (mark[a] == stamp) ++a;
      A[b][c] = a;
      if (a == b && b > c) tau[c] = b;
    }
  }
  // inverse: for each h, P-positions [h,b',c''] with b' < h
  std::vector<std::vector<std::pair<int,int>>> byFirst(4 * N + 10);
  for (int b = 0; b <= N; ++b) for (int c = 0; c <= b; ++c) if (A[b][c] >= 0 && A[b][c] <= N) byFirst[A[b][c]].push_back({b, c});
  std::vector<int> matchedBy(N + 1, -1);  // column -> row
  for (int c = 0; c <= N; ++c) if (tau[c] >= 0) matchedBy[c] = tau[c];
  long long agree = 0, rows = 0, minAvailMatched = 0, failNoAvail = 0, failBlocked = 0;
  std::vector<int> skipHist(20, 0);
  for (int h = 1; h <= N; ++h) {
    // blocked set
    int half = h;  // columns >= half are blocked
    std::vector<char> blk(h + 1, 0);
    for (auto [b, c] : byFirst[h]) {
      if (b >= h) continue;
      if (c < b) blk[c] = 1; else half = std::min(half, b);
    }
    // available: columns c < h with tau[c] >= h or side (tau -1 means unmatched within N)
    int pred = -1, firstAvail = -1, skipped = 0;
    for (int c = 0; c < h; ++c) {
      bool avail = (tau[c] < 0 || tau[c] >= h);
      if (!avail) continue;
      if (firstAvail < 0) firstAvail = c;
      if (c >= half || blk[c]) { ++skipped; continue; }
      pred = c; break;
    }
    int actual = -1;
    for (auto [b, c] : byFirst[h]) if (b == h) actual = c;
    ++rows;
    if (pred == actual) ++agree;
    else if (mode == 0) printf("MISMATCH h=%d predicted %d actual %d\n", h, pred, actual);
    if (actual >= 0) { if (actual == firstAvail) ++minAvailMatched; skipHist[std::min(19, skipped)]++; }
    else { if (firstAvail < 0) ++failNoAvail; else ++failBlocked; }
    if (mode == 1 && h <= 60) {
      printf("h=%d match=%d firstAvail=%d half=%d points:", h, actual, firstAvail, half);
      for (auto [b, c] : byFirst[h]) if (b < h && c < b) printf(" %d", c);
      printf("\n");
    }
  }
  printf("rows %lld, greedy prediction agrees %lld\n", rows, agree);
  printf("matched to least available column: %lld; unmatched rows: %lld with no available column, %lld all blocked\n", minAvailMatched, failNoAvail, failBlocked);
  printf("skipped available columns before the match:"); for (int i = 0; i < 20; ++i) if (skipHist[i]) printf(" %d:%d", i, skipHist[i]); printf("\n");
}
