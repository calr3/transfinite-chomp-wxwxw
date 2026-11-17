// usage: side_ingredients N   (checks Sheiner Lemma 4.2, alive rows, A(a,a) <= 2a+1, tau(r) <= 2r+1)
// Numerical checks of the ingredients of the infinitude argument (N = max second row).
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
  // (1) Lemma 4.2: for non-side r with p = tau(r) and every r < q < p: some b < r has A(q,b) = p;
  //     the b's are distinct; each such b is side or has tau(b) > q.
  long inst = 0, fail42 = 0, faildist = 0, failalive = 0;
  for (int r = 0; r <= N; ++r) {
    int p = tau[r]; if (p < 0 || p > N) continue;
    std::vector<int> used;
    for (int q = r + 1; q < p; ++q) {
      ++inst; int bq = -1;
      for (int b = 0; b < r; ++b) if (A[q][b] == p) { bq = b; break; }
      if (bq < 0) { ++fail42; continue; }
      used.push_back(bq);
      if (!(tau[bq] < 0 || tau[bq] > q)) ++failalive;
    }
    std::sort(used.begin(), used.end());
    if (std::adjacent_find(used.begin(), used.end()) != used.end()) ++faildist;
  }
  printf("Lemma 4.2 instances %ld: missing b %ld, non-distinct %ld, b neither side nor alive %ld\n", inst, fail42, faildist, failalive);
  // (2) A(a,a) <= 2a+1, and {1..a} contained in the blocked set of (a,a)
  int worst = -1 << 30, failB = 0;
  for (int a = 0; a <= N; ++a) {
    worst = std::max(worst, A[a][a] - (2 * a + 1));
    std::vector<char> in(3 * N + 10, 0);
    for (int t = 0; t < a; ++t) in[A[t][t]] = 1;
    for (int b = 0; b < a; ++b) if (A[a][b] >= 0) in[A[a][b]] = 1; else if (tau[b] >= 0) in[tau[b]] = 1;  // f(a,b) = tau(b) if NONE
    for (int k = 1; k <= a; ++k) if (!in[k]) { ++failB; break; }
  }
  printf("max A(a,a) - (2a+1) over a <= %d: %d;  diagonal cells with {1..a} not all blocked: %d\n", N, worst, failB);
  // (3) tau(r) <= 2r+1
  int w3 = -1 << 30; for (int r = 0; r <= N; ++r) if (tau[r] >= 0) w3 = std::max(w3, tau[r] - (2 * r + 1));
  printf("max tau(r) - (2r+1): %d\n", w3);
}
