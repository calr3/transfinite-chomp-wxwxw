// The 2D side class of Huddleston-Shurman, computed from finite 3-row Chomp.
//
// A position [a,b,c] has row lengths a >= b >= c (poison at the start of row 1). For fixed
// (b,c) at most one a >= max(b,1) makes [a,b,c] P; call it A(b,c), or NONE. The options of
// [a,b,c] are
//   * [a',b,c] with b <= a' < a,
//   * [a',a',min(c,a')] with 1 <= a' < b (a bite in row 1 left of b),
//   * [a,b',min(c,b')] with b' < b (a bite in row 2): value A(b',c) if b' >= c, A(b',b') if b' < c,
//   * [a,b,c'] with c' < c (a bite in row 3): value A(b,c').
// So A(b,c) = NONE if some [a',a',min(c,a')] with a' < b is P, i.e. if tau(c) < b below, and
// otherwise A(b,c) is the least a >= max(b,1) not in
//   E(b,c) = {A(b,c') : c' < c} u {A(b',c) : c <= b' < b} u {A(b',b') : b' < c}.
// The side class is S = {x : no h > x with A(h,x) = h}; for x not in S, tau(x) is that h.
//
// Order of computation: the outer loop is c, the inner loop is b = c, c+1, ... The three parts
// of E(b,c) are bitsets over the values a, aligned to 64-bit words: one per row b (filled over
// the earlier stages), one for the current stage's column {A(b',c) : b' < b}, and one for the
// diagonal values. A(b,c) is the first zero of their OR at or after b, found a word at a time.
// A stage stops at b = tau(c), since every larger b gives NONE.
//
// usage: side3row N K [1]   (b <= N; offsets A(b,c) - b must stay below K; 1: also print the
// diagonal values "diag k A(k,k)")
// Output: "side x" for side elements, "tau x h" for the others, both only for x with
// x <= N/2 (tau(x)/x stays near sqrt 2, so a missing tau below N/2 is reliable in practice;
// the program also reports the largest ratio tau(x)/x seen).
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>

int main(int argc, char** argv) {
  if (argc < 3) { std::fprintf(stderr, "usage: side3row N K\n"); return 1; }
  const long long N = std::atoll(argv[1]), K = std::atoll(argv[2]);
  const long long V = N + K + 128;            // values a < V
  const long long VW = V / 64 + 2;            // words of a value bitset
  const long long RW = K / 64 + 3;            // words per row bitset (row b starts at word b/64)
  // rowbits: for row b, bit (a - 64*floor(b/64)) is set iff a = A(b,c') for some earlier c'.
  // Rows are word-aligned with the absolute values, so the three sets can be ORed word by word.
  std::vector<uint64_t> rowbits((size_t)(N + 1) * RW, 0);
  std::vector<uint64_t> diag(VW, 0);          // bit a: a = A(j,j) for some j < c
  std::vector<uint64_t> col(VW, 0);           // bit a: a = A(b',c) for some b' < b (this stage)
  std::vector<int64_t> tau(N + 1, -1), Adiag(N + 1, -1);
  long long words = 0, maxoff = 0, pos = 0;
  double sumoff = 0;

  for (long long c = 0; c <= N; ++c) {
    if (c >= 1 && Adiag[c - 1] >= 0) diag[Adiag[c - 1] >> 6] |= 1ull << (Adiag[c - 1] & 63);
    long long lo = V, hi = 0;                 // words of col touched in this stage
    for (long long b = c; b <= N; ++b) {
      // least a >= max(b,1) outside row b, the column set and the diagonal set
      const uint64_t* row = &rowbits[(size_t)b * RW];
      long long w0 = b >> 6, w = w0;
      uint64_t mask = (1ull << (b & 63)) - 1;
      if (b == 0) mask = 1;                   // a >= 1
      long long a;
      for (;;) {
        if (w - w0 >= RW) { std::fprintf(stderr, "offset beyond K at b=%lld c=%lld; raise K\n", b, c); return 1; }
        uint64_t x = row[w - w0] | col[w] | diag[w] | mask;
        ++words;
        if (x != ~0ull) { a = w * 64 + __builtin_ctzll(~x); break; }
        mask = 0;
        ++w;
      }
      long long off = a - b;
      if (off >= K) { std::fprintf(stderr, "offset %lld >= K at b=%lld c=%lld; raise K\n", off, b, c); return 1; }
      if (off > maxoff) maxoff = off;
      sumoff += off; ++pos;
      rowbits[(size_t)b * RW + ((a >> 6) - w0)] |= 1ull << (a & 63);
      col[a >> 6] |= 1ull << (a & 63);
      if ((a >> 6) < lo) lo = a >> 6;
      if ((a >> 6) > hi) hi = a >> 6;
      if (b == c) Adiag[c] = a;
      if (a == b && b > c) { tau[c] = b; break; }  // larger b: NONE (bite row 1 at b)
    }
    for (long long w = lo; w <= hi; ++w) col[w] = 0;
  }
  double maxratio = 0;
  long long cnt = 0;
  if (argc > 3 && std::atoi(argv[3]) == 1)  // also print the diagonal values A(k,k), k <= N/2
    for (long long k = 0; k <= N / 2; ++k) std::printf("diag %lld %lld\n", k, (long long)Adiag[k]);
  for (long long x = 0; x <= N / 2; ++x) {
    if (tau[x] < 0) { std::printf("side %lld\n", x); ++cnt; }
    else {
      std::printf("tau %lld %lld\n", x, (long long)tau[x]);
      if (x >= 50 && (double)tau[x] / x > maxratio) maxratio = (double)tau[x] / x;
    }
  }
  std::fprintf(stderr, "N=%lld: %lld side elements up to %lld; max tau(x)/x for x >= 50: %.4f; "
               "max offset %lld, mean offset %.1f; %lld positions, %lld word reads\n",
               N, cnt, N / 2, maxratio, maxoff, sumoff / pos, pos, words);
  return 0;
}
