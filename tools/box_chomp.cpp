// Exact solver for finite 3D Chomp on an a x b x c box.
//
// A position is a downset of the box, stored as a plane partition: h[x][y] is the
// number of cells in column (x, y), non-increasing in x and in y. Taking cell
// (x, y, z) sets h[x'][y'] = min(h[x'][y'], z) for all x' >= x, y' >= y. The cell
// (0, 0, 0) is poison: taking it is never a winning move, so it is simply not
// offered, and the position {(0,0,0)} (no other moves) is a loss for the mover.
//
// Usage: box_chomp a b c   -> prints every winning first move (x, y, z).
// Heights are packed into a 64-bit key (bits per column = enough for c), so
// a * b * bits(c) must be <= 64.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <unordered_map>
#include <vector>

static int A, B, C, BITS;
static uint64_t MASK;
static std::unordered_map<uint64_t, bool> memo;  // true = N-position (mover wins)

static inline int get(uint64_t s, int x, int y) {
  return (int)((s >> (BITS * (x * B + y))) & MASK);
}
static inline uint64_t setv(uint64_t s, int x, int y, int v) {
  int sh = BITS * (x * B + y);
  return (s & ~(MASK << sh)) | ((uint64_t)v << sh);
}
static uint64_t chomp(uint64_t s, int x, int y, int z) {
  for (int i = x; i < A; ++i) {
    if (get(s, i, y) <= z) break;  // columns further out in x are no taller
    for (int j = y; j < B; ++j) {
      int h = get(s, i, j);
      if (h <= z) break;
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
  if (argc != 4) { std::fprintf(stderr, "usage: %s a b c\n", argv[0]); return 1; }
  A = std::atoi(argv[1]); B = std::atoi(argv[2]); C = std::atoi(argv[3]);
  BITS = 1; while ((1 << BITS) <= C) ++BITS;
  MASK = (1ull << BITS) - 1;
  if (A * B * BITS > 64) { std::fprintf(stderr, "box too large for 64-bit key\n"); return 1; }
  uint64_t full = 0;
  for (int x = 0; x < A; ++x) for (int y = 0; y < B; ++y) full = setv(full, x, y, C);
  std::printf("%dx%dx%d winning first moves:", A, B, C);
  for (int x = 0; x < A; ++x)
    for (int y = 0; y < B; ++y)
      for (int z = 0; z < C; ++z) {
        if (x == 0 && y == 0 && z == 0) continue;
        if (!win(chomp(full, x, y, z))) std::printf(" (%d,%d,%d)", x, y, z);
      }
  std::printf("   [%zu positions]\n", memo.size());
  return 0;
}
