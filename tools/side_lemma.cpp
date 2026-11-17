// usage: side_lemma N   (lemma L1: every h >= 1 is exactly one of a partner tau(x) or a diagonal value A(k,k))
// Test: (L1) for every h >= 1, h is an image of tau  XOR  h = A(k,k) for some k.
#include <cstdio>
#include <cstdlib>
#include <vector>
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
  std::vector<char> isImg(V, 0), isD(V, 0), isS(N + 1, 0);
  for (int c = 0; c <= N; ++c) if (tau[c] >= 0) isImg[tau[c]] = 1; else isS[c] = 1;
  for (int k = 0; k <= N; ++k) isD[A[k][k]] = 1;
  int H = N / 2;  // images h <= H come from columns < h <= N/2; D values <= H come from k <= H
  int both = 0, neither = 0;
  for (int h = 1; h <= H; ++h) { if (isImg[h] && isD[h]) ++both; if (!isImg[h] && !isD[h]) { ++neither; if (neither < 10) printf("neither: %d\n", h); } }
  printf("h <= %d: both image and diagonal: %d, neither: %d\n", H, both, neither);
  // with L1, images = complement of D. Compare S and D.
  int sd = 0, ns_nd = 0, lead = 0, minlead = 1 << 30;
  for (int x = 0; x <= H; ++x) {
    bool s = isS[x], d = (x >= 1) && isD[x];
    if (s && d) ++sd;
    if (!s && !d && x >= 1) ++ns_nd;
    lead = sd - ns_nd; if (lead < minlead) minlead = lead;
  }
  printf("x <= %d: in S and D: %d; in neither (x>=1): %d; min over v of (#S&D - #neither) = %d\n", H, sd, ns_nd, minlead);
  // A(k,k) - k pattern
  printf("A(k,k) for k<30:"); for (int k = 0; k < 30; ++k) printf(" %d", A[k][k]); printf("\n");
}
