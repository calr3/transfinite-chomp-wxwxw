// usage: side_notboth N   (for diagonal rows h = A(k,k): why each [h,h,x], x < k, is N)
// For h = A(k,k) (diagonal rows), why is [h,h,x] N for every x < k?  Classify the P option used.
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <map>
#include <string>
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
  std::map<std::string, long> why;
  long minMargin = 1L << 40; int argk = -1;
  bool increasing = true;
  for (int k = 1; k <= N / 2; ++k) if (A[k][k] <= A[k-1][k-1]) increasing = false;
  for (int k = 1; k <= N / 2; ++k) {
    int h = A[k][k];
    if (h > N) break;
    for (int x = 0; x < k; ++x) {
      std::string r;
      if (tau[x] >= 0 && tau[x] < h) { r = "row1: [tau(x),tau(x),x] with tau(x) < h"; long m = h - tau[x]; if (m < minMargin) { minMargin = m; argk = k; } }
      else {
        // row-2 bite: [h,b',min(x,b')] P for some b' < h
        int bp = -1;
        for (int b2 = 0; b2 < h && bp < 0; ++b2) { int cc = x < b2 ? x : b2; if (cc <= b2 && A[b2][cc] == h) bp = b2; }
        if (bp >= 0) r = (bp > x ? "row2 point: [h,b',x] P, b' > x" : "row2 diag: [h,b',b'] P, b' <= x");
        else r = "OTHER";
      }
      why[(tau[x] < 0 ? "side x: " : "non-side x: ") + r]++;
    }
  }
  for (auto& [k, v] : why) printf("%8ld  %s\n", v, k.c_str());
  printf("A(k,k) strictly increasing for k <= %d: %s\n", N / 2, increasing ? "yes" : "no");
  printf("min over diagonal rows h=A(k,k) and non-side x<k of h - tau(x): %ld (at k=%d)\n", minMargin, argk);
  // tau(c) < A(c+1,c+1)?
  long bad = 0, minm = 1L << 40;
  for (int c = 0; c < N / 2; ++c) if (tau[c] >= 0) { long m = (long)A[c+1][c+1] - tau[c]; if (m <= 0) ++bad; if (m < minm) minm = m; }
  printf("non-side c with tau(c) >= A(c+1,c+1): %ld; min margin A(c+1,c+1) - tau(c) = %ld\n", bad, minm);
}
