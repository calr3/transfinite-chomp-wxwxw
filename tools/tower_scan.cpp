// Probe whether B x omega is a P-position, for a finite rectangular base B = j x k.
//
// Every option of B x omega is either a finite box B x g (an N-position by strategy
// stealing, except 1x1x1), or a "tower"
//     T(b, g) = B x [0,g)  union  (B \ up(b)) x [g, omega),   b in B \ {0},  g >= 0,
// reached by taking the cell (b, g). B x omega is P iff every tower is N. A tower is N
// in particular if one of its finite truncations
//     T(b, g, t) = B x [0,g)  union  (B \ up(b)) x [g, t),   t > g
// is P (at most one t can work, since T(b,g,t) is an option of T(b,g,t') for t < t').
//
// For each b and g <= G this prints the t <= T with T(b,g,t) P, or "none<=T" if there
// is none. "none" marks a tower that may be P (then B x omega is N); the scan alone
// does not prove it, because a tower also has options that keep an infinite rod.
//
// Usage: tower_scan j k G T
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>

static int A, B, BITS;
static uint64_t MASK;
static std::unordered_map<uint64_t, bool> memo;

static inline int get(uint64_t s, int x, int y) { return (int)((s >> (BITS * (x * B + y))) & MASK); }
static inline uint64_t setv(uint64_t s, int x, int y, int v) {
  int sh = BITS * (x * B + y);
  return (s & ~(MASK << sh)) | ((uint64_t)v << sh);
}
static uint64_t chomp(uint64_t s, int x, int y, int z) {
  for (int i = x; i < A; ++i) {
    if (get(s, i, y) <= z) break;
    for (int j = y; j < B; ++j) {
      if (get(s, i, j) <= z) break;
      s = setv(s, i, j, z);
    }
  }
  return s;
}
static bool win(uint64_t s) {
  auto it = memo.find(s);
  if (it != memo.end()) return it->second;
  bool w = false;
  for (int x = 0; x < A && !w; ++x)
    for (int y = 0; y < B && !w; ++y) {
      int h = get(s, x, y);
      if (h == 0) break;
      for (int z = 0; z < h && !w; ++z) {
        if (x == 0 && y == 0 && z == 0) continue;
        if (!win(chomp(s, x, y, z))) w = true;
      }
    }
  memo.emplace(s, w);
  return w;
}

int main(int argc, char** argv) {
  if (argc != 5) { std::fprintf(stderr, "usage: %s j k G T\n", argv[0]); return 1; }
  A = std::atoi(argv[1]); B = std::atoi(argv[2]);
  int G = std::atoi(argv[3]), T = std::atoi(argv[4]);
  BITS = 1; while ((1 << BITS) <= T) ++BITS;
  MASK = (1ull << BITS) - 1;
  if (A * B * BITS > 64) { std::fprintf(stderr, "too large for 64-bit key\n"); return 1; }
  std::printf("base %dx%d (g <= %d, t <= %d)\n", A, B, G, T);
  for (int bx = 0; bx < A; ++bx)
    for (int by = 0; by < B; ++by) {
      if (bx == 0 && by == 0) continue;
      std::printf("  b=(%d,%d):", bx, by);
      for (int g = 0; g <= G; ++g) {
        int found = -1;
        for (int t = g + 1; t <= T && found < 0; ++t) {
          uint64_t s = 0;
          for (int x = 0; x < A; ++x)
            for (int y = 0; y < B; ++y)
              s = setv(s, x, y, (x >= bx && y >= by) ? g : t);
          if (!win(s)) found = t;
        }
        if (found >= 0) std::printf(" g%d:t=%d", g, found);
        else std::printf(" g%d:none<=%d", g, T);
      }
      std::printf("\n");
    }
  std::fprintf(stderr, "[%zu positions]\n", memo.size());
  return 0;
}
