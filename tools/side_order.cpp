// usage: side_order N   (monotonicity of tau and of A(k,k); margin of tau(x) below A(k,k), k > x)
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
int main(int argc, char** argv) {
  int N = atoi(argv[1]);
  std::vector<std::vector<int>> A(N + 1);
  std::vector<int> tau(N + 1, -1);
  int V = 4 * N + 10; std::vector<int> mark(V, 0); int stamp = 0;
  for (int b = 0; b <= N; ++b) A[b].assign(b + 1, -2);
  for (int c = 0; c <= N; ++c) for (int b = c; b <= N; ++b) {
    if (tau[c] >= 0 && tau[c] < b) { A[b][c] = -1; continue; }
    ++stamp;
    for (int c2 = 0; c2 < c; ++c2) { int v = A[b][c2]; if (v >= 0) mark[v] = stamp; }
    for (int j = c; j < b; ++j) { int v = A[j][c]; if (v >= 0) mark[v] = stamp; }
    for (int j = 0; j < c; ++j) { int v = A[j][j]; if (v >= 0) mark[v] = stamp; }
    int a = b < 1 ? 1 : b; while (mark[a] == stamp) ++a;
    A[b][c] = a; if (a == b && b > c) tau[c] = b;
  }
  int H = N / 2;
  int dec = 0; printf("A(k,k) descents (k: A(k-1,k-1) -> A(k,k)):");
  for (int k = 1; k <= H; ++k) if (A[k][k] < A[k-1][k-1]) { if (dec < 12) printf(" %d:%d->%d", k, A[k-1][k-1], A[k][k]); ++dec; }
  printf("  [%d descents]\n", dec);
  int prev = -1, px = -1, tdec = 0; printf("tau descents over non-side x (x: tau(prev) -> tau(x)):");
  for (int x = 0; x <= H; ++x) if (tau[x] >= 0) { if (prev >= 0 && tau[x] < prev) { if (tdec < 12) printf(" %d:%d->%d", x, prev, tau[x]); ++tdec; } prev = tau[x]; px = x; }
  printf("  [%d descents]\n", tdec);
  // minimal margin: tau(x) < min_{k > x} A(k,k)?
  std::vector<int> sufmin(H + 2, 1 << 30);
  for (int k = H; k >= 0; --k) sufmin[k] = std::min(sufmin[k + 1], A[k][k]);
  int worst = 1 << 30, wx = -1;
  for (int x = 0; x < H; ++x) if (tau[x] >= 0) { int m = sufmin[x + 1] - tau[x]; if (m < worst) { worst = m; wx = x; } }
  printf("min over non-side x of (min_{k>x} A(k,k)) - tau(x) = %d at x=%d\n", worst, wx);
  // greedy order: is tau(x) the n-th image when x is the n-th non-side element?
}
