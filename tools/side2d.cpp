// usage: side2d N   (prints the side class up to N/2 and the partners tau)
// 3-row Chomp [a,b,c] (row lengths, a >= b >= c, poison in row 1). A(b,c) = the unique a >= b
// with [a,b,c] P, or -1. The 2D side class: x such that A(h,x) != h for every h > x.
#include <cstdio>
#include <cstdlib>
#include <vector>
int main(int argc, char** argv) {
  int N = atoi(argv[1]);
  std::vector<std::vector<int>> A(N + 1, std::vector<int>(N + 1, -2));
  std::vector<int> tau(N + 1, -1);  // tau[x] = h with A(h,x) = h
  std::vector<int> mark(4 * N + 10, 0); int stamp = 0;
  for (int b = 0; b <= N; ++b)
    for (int c = 0; c <= b; ++c) {
      // NONE if some j < b has A(j, min(c,j)) == j
      bool none = false;
      for (int j = 1; j < b && !none; ++j) { int cc = c < j ? c : j; if (A[j][cc] == j) none = true; }
      if (b == 0 && c == 0) { A[0][0] = 1; continue; }  // [1,0,0]: poison alone is P (misere)
      if (none) { A[b][c] = -1; continue; }
      ++stamp;
      for (int c2 = 0; c2 < c; ++c2) { int v = A[b][c2]; if (v >= 0 && v < (int)mark.size()) mark[v] = stamp; }
      for (int j = 0; j < b; ++j) { int cc = c < j ? c : j; int v = A[j][cc]; if (v >= 0 && v < (int)mark.size()) mark[v] = stamp; }
      int a = b < 1 ? 1 : b;
      while (a < (int)mark.size() && mark[a] == stamp) ++a;
      A[b][c] = a;
      if (a == b && c < b) tau[c] = b;
    }
  int cnt = 0;
  printf("side:");
  for (int x = 0; x <= N; ++x) if (tau[x] < 0 && x <= N / 2) { printf(" %d", x); ++cnt; }
  printf("\ncount(x <= N/2) = %d\ntau:", cnt);
  for (int x = 0; x <= N / 2; ++x) if (tau[x] >= 0) printf(" %d->%d", x, tau[x]);
  printf("\n");
}
