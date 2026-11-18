// Rod solver: Chomp on S x N with heights in N or omega, for a finite Young diagram S.
// Shared by rodf.cpp (command-line tool) and chomp3p.cpp (as an exact oracle for positions with
// one unbounded axis). See rodf.cpp for the method; in short:
//
//   * f(r): for a finite rest r (heights of the cells other than the poison column), the unique
//     poison height making the position P, or NONE. Exact (completing-height reduction).
//   * pw(h): is (omega, r) P, for a rest r with omega cells? Exact when the omega part is a
//     two-wide stalk (poison + one cell): the cuts of the poison column are decided by
//     simulating a finite system of mex-sequences until its state repeats (additive
//     periodicity, as in Landman's proof for Wythoff's game). Otherwise moves inside omega
//     columns are capped at ALPHA * H + D and the answer is heuristic unless witnessed exactly.
#pragma once
#include <algorithm>
#include <chrono>
#include <cmath>
#include <climits>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <list>
#include <string>
#include <unordered_map>
#include <vector>

#include <fcntl.h>
#include <sys/mman.h>
#include <unistd.h>
#ifdef __BMI2__
#include <immintrin.h>
#endif

namespace rod {

// Storage for the cached offset sequences. By default it is heap memory in 64 MB chunks. With
// Arena::useFile(path) it is a sparse file mapped into memory (MAP_SHARED), so the kernel can
// write cold sequences back to disk and drop them from RAM: the working set of one certificate
// is only its options' sequences. Nothing is ever freed.
struct Arena {
  static Arena& get() { static Arena a; return a; }
  int fd = -1;
  uint8_t* base = nullptr;   // file mode: the reserved mapping
  size_t used = 0, fileSize = 0, reserve = 0;
  std::vector<uint8_t*> chunks;  // heap mode
  size_t chunkLeft = 0;
  uint8_t* chunkPtr = nullptr;
  size_t heapBytes = 0;
  bool useFile(const char* path, size_t reserveBytes = (size_t)1 << 39) {
    fd = ::open(path, O_RDWR | O_CREAT | O_TRUNC, 0600);
    if (fd < 0) return false;
    ::unlink(path);  // the file disappears with the process
    reserve = reserveBytes;
    void* m = ::mmap(nullptr, reserve, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_NORESERVE, fd, 0);
    if (m == MAP_FAILED) { ::close(fd); fd = -1; return false; }
    base = (uint8_t*)m;
    return true;
  }
  uint8_t* alloc(size_t n) {
    n = (n + 7) & ~(size_t)7;
    if (fd >= 0) {
      if (used + n > fileSize) {
        size_t grow = std::max<size_t>((size_t)1 << 30, n);
        if (fileSize + grow > reserve || ::ftruncate(fd, (off_t)(fileSize + grow)) != 0) {
          std::fprintf(stderr, "arena: cannot grow the file to %.1f GB\n", (fileSize + grow) / 1e9);
          std::abort();
        }
        fileSize += grow;
      }
      uint8_t* p = base + used;
      used += n;
      return p;
    }
    if (n > chunkLeft) {
      size_t sz = std::max<size_t>((size_t)64 << 20, n);
      chunkPtr = (uint8_t*)std::calloc(sz, 1);
      if (!chunkPtr) { std::fprintf(stderr, "arena: out of memory\n"); std::abort(); }
      chunks.push_back(chunkPtr);
      chunkLeft = sz;
      heapBytes += sz;
    }
    uint8_t* p = chunkPtr;
    chunkPtr += n;
    chunkLeft -= n;
    used += n;
    return p;
  }
};

using u64 = uint64_t;
static const int OMEGA = 255;
static const uint16_t NONE = 0xFFFF;

struct Key {
  u64 a, b;
  bool operator==(const Key& o) const { return a == o.a && b == o.b; }
};
struct KH {
  size_t operator()(const Key& k) const {
    u64 x = k.a * 0x9E3779B97F4A7C15ull ^ (k.b + 0x632BE59BD9B4E019ull);
    x ^= x >> 29;
    return x * 0xBF58476D1CE4E5B9ull;
  }
};
using H = std::vector<uint8_t>;  // heights of all cells (index 0 = poison column)

// Compact open-addressing map u64 -> u16 for the f-memo when the key fits in 64 bits (at most
// 9 cells). About 14 bytes per entry instead of about 50 for std::unordered_map.
struct FMap {
  static constexpr u64 EMPTY = ~0ull;  // all cells omega: never a finite rest
  std::vector<u64> k;
  std::vector<uint16_t> v;
  size_t cnt = 0, mask = 0;
  FMap() { k.assign(size_t(1) << 16, EMPTY); v.assign(size_t(1) << 16, 0); mask = (size_t(1) << 16) - 1; }
  static size_t hash(u64 x) {
    x ^= x >> 33; x *= 0xff51afd7ed558ccdULL; x ^= x >> 33; x *= 0xc4ceb9fe1a85ec53ULL; x ^= x >> 33;
    return (size_t)x;
  }
  const uint16_t* find(u64 key) const {
    for (size_t i = hash(key) & mask; k[i] != EMPTY; i = (i + 1) & mask)
      if (k[i] == key) return &v[i];
    return nullptr;
  }
  void put(u64 key, uint16_t val) {
    if ((cnt + 1) * 4 > (mask + 1) * 3) grow();
    size_t i = hash(key) & mask;
    for (; k[i] != EMPTY; i = (i + 1) & mask)
      if (k[i] == key) { v[i] = val; return; }
    k[i] = key; v[i] = val; ++cnt;
  }
  void grow() {
    std::vector<u64> ok; std::vector<uint16_t> ov;
    ok.swap(k); ov.swap(v);
    size_t ns = (mask + 1) * 2;
    k.assign(ns, EMPTY); v.assign(ns, 0); mask = ns - 1; cnt = 0;
    for (size_t i = 0; i < ok.size(); ++i) if (ok[i] != EMPTY) put(ok[i], ov[i]);
  }
};

struct Why { int cell, z; bool exact; };
struct Abort {};  // thrown when a call exceeds its work budget (see RodSolver::budgetEnd)
struct TypeIResult { bool decided; bool hasP; int z; int period; int states; };

struct RodSolver {
  int ALPHA = 2, DSLACK = 6, ZSIM = 30000;
  int MSIM = 3000000;  // step limit of a single member's certificate (cheap per step)
  bool EXACT1 = true;
  int NC = 0;
  std::vector<int> cx, cy;
  std::vector<std::vector<int>> up;
  std::vector<int> tperm;
  std::unordered_map<Key, uint16_t, KH> fmemo;  // used when NC > 9
  FMap fmap;                                     // used when NC <= 9
  std::unordered_map<Key, uint8_t, KH> wmemo;  // bit1: P, bit2: exact
  long long fcount = 0, wcount = 0, typeICertified = 0, typeIUncertified = 0;
  long long budgetEnd = -1;  // if >= 0, throw Abort once fcount + wcount exceeds it
  void spend() { if (budgetEnd >= 0 && fcount + wcount > budgetEnd) throw Abort{}; }

  // cols: column heights of S, one digit each, non-increasing
  explicit RodSolver(const std::string& cols) {
    for (int x = 0; x < (int)cols.size(); ++x)
      for (int y = 0; y < cols[x] - '0'; ++y) { cx.push_back(x); cy.push_back(y); ++NC; }
    up.assign(NC, {});
    for (int i = 0; i < NC; ++i)
      for (int j = 0; j < NC; ++j)
        if (cx[j] >= cx[i] && cy[j] >= cy[i]) up[i].push_back(j);
    bool sym = true;
    std::vector<int> t(NC, -1);
    for (int i = 0; i < NC; ++i) {
      for (int j = 0; j < NC; ++j) if (cx[j] == cy[i] && cy[j] == cx[i]) t[i] = j;
      if (t[i] < 0) sym = false;
    }
    if (sym) tperm = t;
  }

  Key key(const H& h) const {  // canonical under transpose when S is symmetric
    u64 a = 0, b = 0, ta = 0, tb = 0;
    for (int i = 1; i < NC; ++i) {
      u64 v = h[i];
      if (i <= 8) a |= v << (8 * (i - 1)); else b |= v << (8 * (i - 9));
    }
    if (!tperm.empty()) {
      for (int i = 1; i < NC; ++i) {
        u64 v = h[tperm[i]];
        if (i <= 8) ta |= v << (8 * (i - 1)); else tb |= v << (8 * (i - 9));
      }
      if (tb < b || (tb == b && ta < a)) { a = ta; b = tb; }
    }
    return {a, b};
  }
  Key rawKey(const H& h) const {
    u64 a = 0, b = 0;
    for (int i = 1; i < NC; ++i) {
      u64 v = h[i];
      if (i <= 8) a |= v << (8 * (i - 1)); else b |= v << (8 * (i - 9));
    }
    return {a, b};
  }
  int restMax(const H& h) const {
    int m = 0;
    for (int i = 1; i < NC; ++i) m = std::max(m, (int)h[i]);
    return m;
  }
  H cut(const H& h, int c, int z) const {
    H g = h;
    for (int j : up[c]) if (g[j] > z) g[j] = z;
    return g;
  }

  void fput(const Key& k, uint16_t v) { if (NC <= 9) fmap.put(k.a, v); else fmemo.emplace(k, v); }
  uint16_t f(const H& h) {  // h: finite rest (h[0] ignored)
    Key k = key(h);
    if (NC <= 9) {
      if (const uint16_t* p = fmap.find(k.a)) return *p;
    } else {
      auto it = fmemo.find(k);
      if (it != fmemo.end()) return it->second;
    }
    ++fcount;
    spend();
    int m = restMax(h);
    for (int z = 1; z < m; ++z) {
      H g = cut(h, 0, z);
      if (f(g) == z) { fput(k, NONE); return NONE; }
    }
    std::vector<uint16_t> E;
    for (int c = 1; c < NC; ++c)
      for (int z = 0; z < h[c]; ++z) {
        uint16_t v = f(cut(h, c, z));
        if (v != NONE) E.push_back(v);
      }
    std::sort(E.begin(), E.end());
    int a = std::max(1, m);
    for (uint16_t v : E) {
      if (v < a) continue;
      if (v == a) ++a; else break;
    }
    fput(k, (uint16_t)a);
    return (uint16_t)a;
  }

  // Cache of certified sequences F_R(z) = f(c at z, R), keyed by R (with c marked OMEGA).
  // F_R is intrinsic to R, so a sequence certified inside one closed family can be reused in
  // any later family. Stored: explicit values for z in [start, start+len) (-1 = NONE), and from
  // z1 on the offsets F(z) - z repeat with period p (NONE repeats too).
  // Stored: the offsets F(z) - z for z in [start, start + off.size()) (NONE16 = NONE), and from
  // z1 on the offsets repeat with period p (NONE repeats too).
  static constexpr int16_t NONE16 = INT16_MIN;
  // Offsets are stored packed: w bits each (w = 4, 5 or 6, the all-ones value = NONE) when every
  // offset is between 0 and 2^w - 2, else 8 bits (-128 = NONE), else 16 bits. Offsets are
  // non-negative mex values, so the small widths cover almost everything; they cut the memory of
  // the cache by about 40% against 8 bits.
  // A sequence of offsets F(z) - z (NONE16 = NONE). Two encodings, both stored in the arena:
  //   * rank code (w = RANK): the offsets of a mex-sequence never lie in the member's own pending
  //     set X (the offsets still blocked by its earlier values), and X is a function of the earlier
  //     offsets. So each offset is stored as its rank among the values not in X, in a Golomb-Rice
  //     code with parameter 2 (about 2.6 bits per offset instead of 4-5). NONE only occurs as a
  //     suffix (after an offset 0, or from the start) and is stored as its start index m.
  //     Decoding is sequential: checkpoints (bit position, X) every CP entries and at the start of
  //     the periodic part, and a cursor per sequence make the solver's sequential reads O(1).
  //   * packed (w = 4, 5, 6: w bits each, all-ones = NONE; w = 8: int8, -128 = NONE; w = 16: int16),
  //     used when the rank code does not apply (an offset >= 127, or NONE not a suffix).
  static constexpr int RANK = 100, CP = 2048;
  using u128 = unsigned __int128;
  struct CPoint { u64 bit; u64 xlo, xhi; u64 pad; };
  static inline void orBits(uint8_t* d, u64& bit, u64 val, int len) {  // len <= 63, d zeroed
    u64 a, b;
    std::memcpy(&a, d + (bit >> 3), 8);
    std::memcpy(&b, d + (bit >> 3) + 8, 8);
    int sh = bit & 7;
    a |= val << sh;
    if (sh) b |= val >> (64 - sh);
    std::memcpy(d + (bit >> 3), &a, 8);
    std::memcpy(d + (bit >> 3) + 8, &b, 8);
    bit += len;
  }
  static void putBits(uint8_t* d, u64& bit, u64 val, int len) {
    for (int j = 0; j < len; ++j, ++bit) if ((val >> j) & 1) d[bit >> 3] |= (uint8_t)(1u << (bit & 7));
  }
  static inline int select64(u64 x, int k) {  // index of the k-th (0-based) set bit of x
#ifdef __BMI2__
    return __builtin_ctzll(_pdep_u64((u64)1 << k, x));
#else
    for (int j = 0; j < k; ++j) x &= x - 1;
    return __builtin_ctzll(x);
#endif
  }
  static inline int selectZero(u128 X, int k) {  // index of the k-th (0-based) zero bit of X
    u64 lo = ~(u64)X;
    if (k == 0) return __builtin_ctzll(lo);  // lo == 0 only if X has 64 low bits set: impossible
    int c = __builtin_popcountll(lo);
    if (k < c) return select64(lo, k);
    return 64 + select64(~(u64)(X >> 64), k - c);
  }
  struct OffVec {
    const uint8_t* d = nullptr;
    const CPoint* cps = nullptr;  // rank code: checkpoints at 0, CP, 2CP, ... and (last) at wrapIdx
    int w = 8, n = 0, m = 0, wrapIdx = -1, ncp = 0;
    size_t nb = 0;  // rank code: bytes used in the arena
    // cursor (rank code): the state before decoding entry cur
    mutable int cur = -1;
    mutable u64 cbit = 0;
    mutable u128 cX = 0;
    OffVec() {}
    OffVec(const std::vector<int16_t>& v, int wrap = -1) {
      n = v.size();
      if (rankEncode(v, wrap)) return;
      int mx = 0;
      bool neg = false;
      for (int16_t x : v) if (x != NONE16) { mx = std::max(mx, (int)x); if (x < 0) neg = true; }
      if (neg || mx > 126) {
        bool wide = false;
        for (int16_t x : v) if (x != NONE16 && (x < -127 || x > 127)) wide = true;
        w = wide ? 16 : 8;
      } else {
        w = mx <= 14 ? 4 : mx <= 30 ? 5 : mx <= 62 ? 6 : 8;
      }
      if (w == 16) {
        int16_t* q = (int16_t*)Arena::get().alloc((size_t)n * 2);
        for (int i = 0; i < n; ++i) q[i] = v[i];
        d = (const uint8_t*)q;
        return;
      }
      if (w == 8) {
        int8_t* q = (int8_t*)Arena::get().alloc((size_t)n);
        for (int i = 0; i < n; ++i) q[i] = v[i] == NONE16 ? -128 : (int8_t)v[i];
        d = (const uint8_t*)q;
        return;
      }
      int none = (1 << w) - 1;
      uint8_t* pk = Arena::get().alloc(((size_t)n * w + 7) / 8 + 2);
      for (int i = 0; i < n; ++i) {
        unsigned val = v[i] == NONE16 ? none : (unsigned)v[i];
        long long bit = (long long)i * w;
        unsigned win = val << (bit & 7);
        pk[bit >> 3] |= win & 0xFF;
        pk[(bit >> 3) + 1] |= (win >> 8) & 0xFF;
      }
      d = pk;
    }
    bool rankEncode(const std::vector<int16_t>& v, int wrap) {
      // validity: offsets in [0,126], never in X, NONE exactly a suffix starting after a 0 or at 0
      int mm = n;
      for (int i = 0; i < n; ++i) if (v[i] == NONE16) { mm = i; break; }
      for (int i = mm; i < n; ++i) if (v[i] != NONE16) return false;
      if (mm > 0 && mm < n && v[mm - 1] != 0) return false;
      u128 X = 0;
      u64 bits = 0;
      std::vector<int> ranks(mm);
      for (int i = 0; i < mm; ++i) {
        int o = v[i];
        if (o < 0 || o > 126 || ((X >> o) & 1)) return false;
        if (o == 0 && i != mm - 1) return false;
        u128 below = o ? (X & ((((u128)1) << o) - 1)) : 0;
        int k = o - __builtin_popcountll((u64)below) - __builtin_popcountll((u64)(below >> 64));
        ranks[i] = k;
        bits += (k >> 1) + 2;
        if (o >= 1) X = (X >> 1) | ((u128)1 << (o - 1));
      }
      m = mm;
      wrapIdx = (wrap >= 0 && wrap < m) ? wrap : -1;
      ncp = (m + CP - 1) / CP + 1;  // regular checkpoints, then the wrap checkpoint slot
      size_t cpBytes = (size_t)ncp * sizeof(CPoint), blob = (bits + 7) / 8 + 16;
      nb = cpBytes + blob;
      uint8_t* mem = Arena::get().alloc(nb);
      CPoint* cp = (CPoint*)mem;
      uint8_t* dd = mem + cpBytes;
      X = 0;
      u64 bit = 0;
      for (int i = 0; i < mm; ++i) {
        if (i % CP == 0) cp[i / CP] = CPoint{bit, (u64)X, (u64)(X >> 64), 0};
        if (i == wrapIdx) cp[ncp - 1] = CPoint{bit, (u64)X, (u64)(X >> 64), 0};
        int k = ranks[i], q = k >> 1;
        // q ones, a zero, then the low bit of k: q + 2 <= 65 bits, written in at most two words
        if (q <= 61) orBits(dd, bit, (((u64)1 << q) - 1) | ((u64)(k & 1) << (q + 1)), q + 2);
        else { putBits(dd, bit, ~(u64)0, q); putBits(dd, bit, 0, 1); putBits(dd, bit, (u64)(k & 1), 1); continue; }
        int o = v[i];
        if (o >= 1) X = (X >> 1) | ((u128)1 << (o - 1));
      }
      d = dd; cps = cp; w = RANK;
      // round trip: decode everything (from the start, and from the wrap checkpoint) and compare
      std::vector<int8_t> back(n);
      decodeTo(0, n, back.data());
      for (int i = 0; i < n; ++i) {
        int16_t want = v[i];
        int8_t got = back[i];
        if ((want == NONE16 && got != -1) || (want != NONE16 && got != want)) {
          std::fprintf(stderr, "rank code round trip failed at %d of %d\n", i, n);
          std::abort();
        }
      }
      if (wrapIdx >= 0) {
        decodeTo(wrapIdx, n, back.data());
        for (int i = wrapIdx; i < n; ++i)
          if (back[i - wrapIdx] != (v[i] == NONE16 ? -1 : v[i])) { std::fprintf(stderr, "rank code wrap check failed\n"); std::abort(); }
      }
      // the cursor decoder (operator[], used by seqValue and the member's own scan): sequentially,
      // then from the wrap point, then the last entry by a fresh seek
      for (int i = 0; i < n; ++i)
        if ((*this)[i] != v[i]) { std::fprintf(stderr, "rank code cursor check failed at %d\n", i); std::abort(); }
      if (wrapIdx >= 0)
        for (int i = wrapIdx; i < n; ++i)
          if ((*this)[i] != v[i]) { std::fprintf(stderr, "rank code cursor wrap check failed\n"); std::abort(); }
      cur = -1;
      if (n > 0 && (*this)[n - 1] != v[n - 1]) { std::fprintf(stderr, "rank code seek check failed\n"); std::abort(); }
      cur = -1;
      return true;
    }
    size_t size() const { return n; }
    size_t bytes() const {
      if (w == RANK) return nb;
      return w <= 6 ? ((size_t)n * w + 7) / 8 + 2 : (size_t)n * (w / 8);
    }
    inline u64 word(u64 bit) const {  // 64 bits starting at bit
      u64 a, b;
      std::memcpy(&a, d + (bit >> 3), 8);
      std::memcpy(&b, d + (bit >> 3) + 8, 8);
      int sh = bit & 7;
      return sh ? (a >> sh) | (b << (64 - sh)) : a;
    }
    void seek(int idx) const {
      int c = idx / CP;
      const CPoint* best = &cps[c];
      int bi = c * CP;
      if (wrapIdx >= 0 && wrapIdx <= idx && wrapIdx > bi) { best = &cps[ncp - 1]; bi = wrapIdx; }
      cur = bi; cbit = best->bit; cX = ((u128)best->xhi << 64) | best->xlo;
    }
    inline int decodeOne() const {  // decode entry cur and advance
      u64 wd;
      std::memcpy(&wd, d + (cbit >> 3), 8);
      wd >>= (cbit & 7);  // at least 57 valid bits
      int q = __builtin_ctzll(~wd);  // number of leading ones
      if (q > 54) { wd = word(cbit); q = __builtin_ctzll(~wd); }
      int k = 2 * q + (int)((wd >> (q + 1)) & 1);
      cbit += q + 2;
      int o = selectZero(cX, k);
      if (o >= 1) cX = (cX >> 1) | ((u128)1 << (o - 1));
      ++cur;
      return o;
    }
    int16_t operator[](size_t ii) const {
      if (w == RANK) {
        int idx = (int)ii;
        if (idx >= m) return NONE16;
        if (cur < 0 || idx < cur || idx - cur > CP) seek(idx);
        while (cur < idx) decodeOne();
        return (int16_t)decodeOne();
      }
      if (w <= 6) {
        long long bit = (long long)ii * w;
        unsigned win = d[bit >> 3] | ((unsigned)d[(bit >> 3) + 1] << 8);
        unsigned val = (win >> (bit & 7)) & ((1u << w) - 1);
        return val == (1u << w) - 1 ? NONE16 : (int16_t)val;
      }
      if (w == 8) { int8_t x = (int8_t)d[ii]; return x == -128 ? NONE16 : (int16_t)x; }
      return ((const int16_t*)d)[ii];
    }
    // entries [from, to) as int8: the offset if 0 <= offset < 128, else -1 (NONE, negative or
    // too large: such entries never block a value in the fast certificate)
    void decodeTo(int from, int to, int8_t* out) const {
      if (w == RANK) {
        int i = from, top = std::min(to, m);
        if (i < top) {
          // local state only: out (int8_t*) may alias anything, so no member is touched in the loop
          int c = i / CP, ci = c * CP;
          const CPoint* best = &cps[c];
          if (wrapIdx >= 0 && wrapIdx <= i && wrapIdx > ci) { best = &cps[ncp - 1]; ci = wrapIdx; }
          u64 bit = best->bit, xlo = best->xlo, xhi = best->xhi;
          const uint8_t* dd = d;
          for (int j = ci; j < top; ++j) {
            u64 wd;
            std::memcpy(&wd, dd + (bit >> 3), 8);
            wd >>= (bit & 7);
            int q = __builtin_ctzll(~wd);
            if (q > 54) { wd = word(bit); q = __builtin_ctzll(~wd); }
            int k = 2 * q + (int)((wd >> (q + 1)) & 1);
            bit += q + 2;
            u64 zl = ~xlo;
            int pc = __builtin_popcountll(zl);
            int o = k < pc ? select64(zl, k) : 64 + select64(~xhi, k - pc);
            if (j >= i) out[j - from] = (int8_t)o;
            if (o >= 1) {  // X = (X >> 1) | 1 << (o - 1)
              xlo = (xlo >> 1) | (xhi << 63);
              xhi >>= 1;
              if (o - 1 < 64) xlo |= (u64)1 << (o - 1); else xhi |= (u64)1 << (o - 65);
            }
          }
          i = top;
        }
        for (; i < to; ++i) out[i - from] = -1;
        return;
      }
      for (int i = from; i < to; ++i) {
        int16_t o = (*this)[i];
        out[i - from] = (o >= 0 && o < 128) ? (int8_t)o : (int8_t)-1;
      }
    }
    bool operator==(const std::vector<int16_t>& v) const {
      if (v.size() != size()) return false;
      for (size_t i = 0; i < v.size(); ++i) if ((*this)[i] != v[i]) return false;
      return true;
    }
  };
  // Decoded sequences (int8: offset, or -1 = never blocks), kept in an LRU pool of bounded size so
  // that the many certificates reading the same option decode it once. Entries used by the
  // certificate in progress are pinned (gen == curGen) and never evicted during it.
  struct Dec { std::vector<int8_t> v; long long gen; std::list<const OffVec*>::iterator it; };
  std::unordered_map<const OffVec*, Dec> decCache;
  std::list<const OffVec*> decLRU;
  size_t decBytes = 0, DECCAP = (size_t)1 << 30;
  long long curGen = 0, decHits = 0, decMiss = 0;
  const int8_t* decoded(const OffVec* o) {
    auto it = decCache.find(o);
    if (it != decCache.end()) {
      ++decHits;
      decLRU.splice(decLRU.begin(), decLRU, it->second.it);
      it->second.gen = curGen;
      return it->second.v.data();
    }
    ++decMiss;
    while (decBytes + o->size() > DECCAP && !decLRU.empty()) {
      const OffVec* victim = decLRU.back();
      auto vt = decCache.find(victim);
      if (vt->second.gen == curGen) break;  // everything older is pinned too? stop evicting
      decBytes -= vt->second.v.size();
      decLRU.pop_back();
      decCache.erase(vt);
    }
    decLRU.push_front(o);
    Dec& dc = decCache[o];
    dc.v.resize(o->size());
    o->decodeTo(0, o->size(), dc.v.data());
    dc.gen = curGen;
    dc.it = decLRU.begin();
    decBytes += dc.v.size();
    return dc.v.data();
  }
  struct Seq {
    int start; OffVec off; int z1, p;
    int scan = INT_MIN;  // typeI's answer for the member itself, once computed: P height, or -1
  };
  std::unordered_map<Key, Seq, KH> seqCache;
  long long seqHits = 0, seqStored = 0;
  long long HISTCAP = 60000000;  // max offsets recorded per certificate (16-bit each)

  int seqValue(const Seq& sq, const H& r, int cIdx, int z) {
    if (z < sq.start) {  // before the cached range: compute directly (finite, exact)
      H g = r;
      g[cIdx] = (uint8_t)z;
      uint16_t v = f(g);
      return v == NONE ? -1 : v;
    }
    int len = sq.off.size();
    int zz = z < sq.start + len ? z : sq.z1 + ((z - sq.z1) % sq.p);
    int16_t o = sq.off[zz - sq.start];
    return o == NONE16 ? -1 : z + o;
  }

  // Certify one member R on its own, bottom-up: every option R' of R (a cut of a finite cell
  // other than c) is certified first and read from the cache, so only R's own state is
  // simulated: its NONE flag, its pending offsets and the phase z mod L of its options' periods.
  // Returns the cached sequence of F_R, or nullptr if some certificate did not close.
  bool PERMEMBER = true;
  long long memberCertified = 0, memberFailed = 0;
  std::unordered_map<Key, char, KH> memberFail;
  // Progress report on stderr every PROGRESS seconds (0 = off): members certified, simulated
  // steps, and the largest period / option-period lcm met so far.
  int PROGRESS = 0;
  long long certSteps = 0, certCalls = 0, maxL = 0;
  int maxP = 0;
  std::chrono::steady_clock::time_point t0 = std::chrono::steady_clock::now(), tLast = t0;
  void report() {
    if (!PROGRESS || (++certCalls & 255)) return;
    auto now = std::chrono::steady_clock::now();
    if (std::chrono::duration<double>(now - tLast).count() < PROGRESS) return;
    tLast = now;
    std::fprintf(stderr, "[%.0fs] f %lld, w %lld, members %lld ok / %lld failed, steps %lld, max period %d, max lcm %lld\n",
                 std::chrono::duration<double>(now - t0).count(), fcount, wcount, memberCertified, memberFailed,
                 certSteps, maxP, maxL);
    memReport();
  }
  // Compressibility of the cached sequences (diagnostic): duplicates, dominant value, runs,
  // exceptions to the dominant value, and the zeroth-order entropy of the offsets.
  void seqStats() {
    std::unordered_map<u64, int> dup;
    double total = 0, distinctOffsets = 0, modeHits = 0, runs = 0, bitsEntropy = 0;
    long long nd = 0;
    std::vector<long long> hist(64, 0);
    for (auto& kv : seqCache) {
      const Seq& sq = kv.second;
      int n = sq.off.n;
      u64 h = 0x9E3779B97F4A7C15ull ^ ((u64)sq.start << 1) ^ ((u64)sq.z1 << 21) ^ ((u64)sq.p << 41);
      std::vector<int> cnt(64, 0);
      int prev = INT_MIN;
      for (int i = 0; i < n; ++i) {
        int o = sq.off[i];
        h = (h ^ (u64)(o + 1)) * 0x100000001B3ull;
        int c = o == NONE16 ? 63 : std::min(o, 62);
        ++cnt[c]; ++hist[c];
        if (o != prev) { ++runs; prev = o; }
      }
      total += n;
      int mx = 0; for (int c : cnt) mx = std::max(mx, c);
      modeHits += mx;
      if (dup.emplace(h, n).second) { ++nd; distinctOffsets += n; }
    }
    for (long long c : hist) if (c) { double q = c / total; bitsEntropy -= c * std::log2(q); }
    // rank coding: o(z) as its rank among the values not in the member's own pending set X(z)
    std::vector<long long> rk(130, 0);
    double rn = 0, bad = 0;
    for (auto& kv : seqCache) {
      const Seq& sq = kv.second;
      unsigned __int128 X = 0;
      bool none = false;
      for (int i = 0; i < sq.off.n; ++i) {
        int o = sq.off[i];
        if (o == NONE16) { ++rk[129]; ++rn; none = true; continue; }
        if (none || o < 0 || o >= 127) { ++bad; continue; }
        int k = 0;
        for (int v = 0; v < o; ++v) if (!((X >> v) & 1)) ++k;
        if ((X >> o) & 1) ++bad;
        ++rk[std::min(k, 128)]; ++rn;
        if (o == 0) { none = true; X = 0; continue; }
        X = (X >> 1) | ((unsigned __int128)1 << (o - 1));
      }
    }
    double re = 0;
    for (long long c : rk) if (c) { double q = c / rn; re -= c * std::log2(q); }
    std::fprintf(stderr, "  rank coding: entropy %.2f bits/offset; ranks 0..5: %.1f%% %.1f%% %.1f%% %.1f%% %.1f%% %.1f%%; inconsistent %.0f\n",
                 re / rn, 100.0 * rk[0] / rn, 100.0 * rk[1] / rn, 100.0 * rk[2] / rn, 100.0 * rk[3] / rn, 100.0 * rk[4] / rn,
                 100.0 * rk[5] / rn, bad);
    std::fprintf(stderr, "  seq stats: %zu members, %lld distinct sequences (%.3g of %.3g offsets distinct); "
                 "dominant value %.1f%% of offsets; %.3g runs; order-0 entropy %.2f bits/offset\n",
                 seqCache.size(), nd, distinctOffsets, total, 100.0 * modeHits / total, runs, bitsEntropy / total);
  }
  // Memory breakdown (estimates from container sizes) and the resident size, on stderr.
  void memReport() {
    double fm = (double)(fmap.mask + 1) * (sizeof(u64) + sizeof(uint16_t));
    double wm = (double)wmemo.size() * 32 + (double)wmemo.bucket_count() * 8;
    double offBytes = 0, offN = 0, maxLen = 0;
    long long wcnt[17] = {0};
    for (auto& kv : seqCache) {
      const OffVec& o = kv.second.off;
      offBytes += o.bytes();
      offN += o.n;
      maxLen = std::max(maxLen, (double)o.n);
      ++wcnt[o.w == RANK ? 0 : o.w];
    }
    double sm = (double)seqCache.size() * (sizeof(Seq) + sizeof(Key) + 16) + (double)seqCache.bucket_count() * 8;
    double mf = (double)memberFail.size() * 40 + (double)memberFail.bucket_count() * 8;
    long rss = 0;
    if (FILE* fp = std::fopen("/proc/self/statm", "r")) { long a, b; if (std::fscanf(fp, "%ld %ld", &a, &b) == 2) rss = b; std::fclose(fp); }
    std::fprintf(stderr, "  mem: arena %.2f GB (%s) | rss %.2f GB | fmap %.0f entries %.2f GB | wmemo %zu %.2f GB | seqCache %zu members: "
                 "nodes %.2f GB + offsets %.2f GB (%.3g offsets, max length %.0f; widths rank:%lld 4:%lld 5:%lld 6:%lld 8:%lld 16:%lld) | memberFail %zu %.2f GB\n",
                 Arena::get().used / 1e9, Arena::get().fd >= 0 ? "file" : "heap", rss * 4096.0 / 1e9, (double)fmap.cnt, fm / 1e9, wmemo.size(), wm / 1e9, seqCache.size(), sm / 1e9,
                 offBytes / 1e9, offN, maxLen, wcnt[0], wcnt[4], wcnt[5], wcnt[6], wcnt[8], wcnt[16], memberFail.size(), mf / 1e9);
  }
  const Seq* certify(const H& r, int cIdx) {
    Key k = rawKey(r);
    auto it = seqCache.find(k);
    if (it != seqCache.end()) return &it->second;
    if (memberFail.count(k)) return nullptr;
    spend();
    report();
    std::vector<const Seq*> os;
    std::vector<H> oh;
    for (int d = 1; d < NC; ++d) {
      if (d == cIdx || r[d] == OMEGA) continue;
      for (int z = 0; z < r[d]; ++z) {
        H g = cut(r, d, z);
        const Seq* sq = certify(g, cIdx);
        if (!sq) { memberFail.emplace(k, 1); return nullptr; }
        os.push_back(sq);
        oh.push_back(g);
      }
    }
    int H0 = 0;
    for (int i = 1; i < NC; ++i) if (i != cIdx && r[i] != OMEGA) H0 = std::max(H0, (int)r[i]);
    bool none = false;
    for (int z = 1; z <= H0 && !none; ++z) {
      H g = r;
      g[cIdx] = (uint8_t)z;
      for (int i = 1; i < NC; ++i) if (i != cIdx && g[i] > z) g[i] = z;
      if (f(g) == z) none = true;
    }
    std::vector<int> consts;
    int maxConst = 0;
    for (int z = 0; z <= H0; ++z) {
      H g = r;
      g[cIdx] = (uint8_t)z;
      for (int j : up[cIdx]) if (g[j] > z) g[j] = z;
      uint16_t v = f(g);
      if (v != NONE) { consts.push_back(v); maxConst = std::max(maxConst, (int)v); }
    }
    long long L = 1;
    int Zc = 0;
    for (const Seq* sq : os) {
      long long p = sq->p, a = L, b = p;
      while (b) { long long t = a % b; a = b; b = t; }
      L = std::min<long long>(L / a * p, 1000000007LL);
      Zc = std::max(Zc, sq->start + (int)sq->off.size());
    }
    maxL = std::max(maxL, L);
    Seq fastSeq;
    int fastR = -1;
    if (FASTCERT && L <= MSIM) {
      fastR = certifyFast(k, os, H0, none, consts, maxConst, L, Zc);
      if (fastR == 1 && CHECKFAST) {  // test mode: redo with the general simulation and compare
        fastSeq = seqCache.find(k)->second;
        seqCache.erase(k);
        --memberCertified; --seqStored;
        checkLimit = 3 * MSIM;  // the fast search may close beyond MSIM; let the general one too
      } else if (fastR == 1) {
        return &seqCache.find(k)->second;
      } else if (fastR == 0 && !CHECKFAST) {
        ++memberFailed; memberFail.emplace(k, 1); return nullptr;
      }
      if (fastR == 2) ++fastOverflow;  // an offset of 128 or more: use the general simulation
    }
    std::vector<int> X;
    std::vector<int16_t> hist;  // offsets F(z) - z for z = H0+1, ...
    std::unordered_map<std::string, int> seen;
    int glim = checkLimit > 0 ? checkLimit : MSIM;
    checkLimit = 0;
    if (L <= glim) {
      for (int z = H0 + 1; z <= glim; ++z) {
        ++certSteps;
        if (z > maxConst + 1 && z >= Zc) {
          std::string st = std::to_string(z % L) + (none ? "N" : "L");
          for (int o : X) { st += std::to_string(o); st.push_back(','); }
          auto jt = seen.find(st);
          if (jt != seen.end()) {
            int z1 = jt->second, p = z - z1;
            int i1 = z1 - (H0 + 1), d = p;
            for (int dd = 1; dd < p; ++dd) {
              if (p % dd) continue;
              bool ok = true;
              for (int j = 0; j < p && ok; ++j) ok = hist[i1 + j] == hist[i1 + (j + dd) % p];
              if (ok) { d = dd; break; }
            }
            while (i1 > 0 && hist[i1 - 1] == hist[i1 - 1 + d]) --i1;
            hist.resize(i1 + d);
            ++memberCertified;
            ++seqStored;
            maxP = std::max(maxP, d);
            if (CHECKFAST && fastR != 2) {
              bool same = fastR == 1 && fastSeq.start == H0 + 1 && fastSeq.off == hist &&
                          fastSeq.z1 == H0 + 1 + i1 && fastSeq.p == d;
              if (!same) { std::fprintf(stderr, "CHECKFAST mismatch (fast result %d)\n", fastR); std::abort(); }
              ++fastChecked;
            }
            return &seqCache.emplace(k, Seq{H0 + 1, OffVec(hist, i1), H0 + 1 + i1, d}).first->second;
          }
          seen.emplace(st, z);
        }
        if (none) { hist.push_back(NONE16); continue; }
        std::vector<int> ex = X;
        for (size_t i = 0; i < os.size(); ++i) {
          int fr = seqValue(*os[i], oh[i], cIdx, z);
          if (fr >= 0) ex.push_back(fr - z);
        }
        for (int cst : consts) if (cst >= z) ex.push_back(cst - z);
        std::sort(ex.begin(), ex.end());
        int o = 0;
        for (int e : ex) { if (e < o) continue; if (e == o) ++o; else break; }
        if (o > 32767) break;
        hist.push_back((int16_t)o);
        if (o == 0) { none = true; X.clear(); continue; }
        std::vector<int> nx;
        for (int e : X) if (e >= 1) nx.push_back(e - 1);
        nx.push_back(o - 1);
        std::sort(nx.begin(), nx.end());
        nx.erase(std::unique(nx.begin(), nx.end()), nx.end());
        X = nx;
      }
    }
    if (CHECKFAST && fastR == 1) { std::fprintf(stderr, "CHECKFAST mismatch (fast certified, general not)\n"); std::abort(); }
    ++memberFailed;
    memberFail.emplace(k, 1);
    return nullptr;
  }

  // The same simulation as in certify, with the state held in bit masks: offsets and the
  // pending set X are kept as 128-bit masks, the options' sequences are read through running
  // indices instead of a modulo, and the visited states are keyed by (z mod L, X) exactly.
  // Returns 1 (certified and stored), 0 (no repeat within MSIM steps) or 2 (an offset reached
  // 128: the caller falls back to the general simulation).
  bool FASTCERT = true, CHECKFAST = false;
  int checkLimit = 0;  // test mode only: step limit of the general simulation for one member
  long long fastOverflow = 0, fastChecked = 0;
  struct SKey {
    u64 a, b, c;
    bool operator==(const SKey& o) const { return a == o.a && b == o.b && c == o.c; }
  };
  struct SKH {
    size_t operator()(const SKey& k) const {
      u64 x = k.a * 0x9E3779B97F4A7C15ull ^ (k.b + 0x632BE59BD9B4E019ull);
      x ^= x >> 31;
      x = x * 0xBF58476D1CE4E5B9ull ^ (k.c * 0x94D049BB133111EBull);
      x ^= x >> 29;
      return x;
    }
  };
  int certifyFast(const Key& k, const std::vector<const Seq*>& os, int H0, bool none,
                  const std::vector<int>& consts, int maxConst, long long L, int Zc) {
    using u128 = unsigned __int128;
    int n = os.size();
    std::vector<int> pos(n), len(n), wrap(n);
    std::vector<const OffVec*> off(n);
    int z0 = H0 + 1;
    for (int i = 0; i < n; ++i) {
      const Seq& sq = *os[i];
      off[i] = &sq.off;
      len[i] = sq.off.size();
      wrap[i] = sq.z1 - sq.start;
      // index of z0 in the option's offsets (z0 >= start: an option's finite part is no taller)
      int zz = z0 < sq.start + len[i] ? z0 : sq.z1 + (z0 - sq.z1) % sq.p;
      if (z0 < sq.start) return 2;
      pos[i] = zz - sq.start;
    }
    // each option's offsets, decoded (or taken from the pool of decoded sequences)
    ++curGen;
    std::vector<const int8_t*> sc(n);
    for (int i = 0; i < n; ++i) sc[i] = decoded(off[i]);
    std::vector<int16_t> hist;
    SKey ck{0, 0, 0};
    int zc = -1;
    long long power = 1;
    u128 X = 0;
    // Options inside their periodic part are merged by period p into one cyclic table of p
    // masks (gt), read at a running phase (gph), so a step costs one lookup per distinct period.
    std::vector<int> gp, gph, pend;
    std::vector<std::vector<u128>> gt;
    std::unordered_map<int, int> gi;
    auto addToGroup = [&](int i) {  // option i is periodic from the current height on
      int p = os[i]->p;
      auto it = gi.find(p);
      if (it == gi.end()) {
        it = gi.emplace(p, (int)gp.size()).first;
        gp.push_back(p);
        gt.emplace_back(p, (u128)0);
        gph.push_back(0);
      }
      std::vector<u128>& tab = gt[it->second];
      int ph = gph[it->second], q = pos[i];
      const int8_t* si = sc[i];
      for (int t = 0; t < p; ++t) {
        int o = si[q];
        if (o >= 0) tab[ph] |= (u128)1 << o;
        if (++q == len[i]) q = wrap[i];
        if (++ph == p) ph = 0;
      }
    };
    for (int i = 0; i < n; ++i) {
      if (z0 >= os[i]->z1) addToGroup(i);
      else pend.push_back(i);
    }
    auto finish = [&](int i1, int d) {
      while (i1 > 0 && hist[i1 - 1] == hist[i1 - 1 + d]) --i1;
      hist.resize(i1 + d);
      ++memberCertified;
      ++seqStored;
      maxP = std::max(maxP, d);
      seqCache.emplace(k, Seq{z0, OffVec(hist, i1), z0 + i1, d});
      return 1;
    };
    long long zlim = 3LL * MSIM;  // Brent may need up to about 3x the steps of a stored-state search
    for (int z = z0; z <= zlim; ++z) {
      ++certSteps;
      if (none) {  // F is NONE from here on: period 1
        hist.push_back(NONE16);
        return finish((int)hist.size() - 1, 1);
      }
      if (z > maxConst + 1 && z >= Zc) {
        // Brent's cycle detection on the state (z mod L, X): the simulation is autonomous from
        // here on, so a state seen again repeats forever. The saved state sits at height zc and
        // moves to the current height whenever the distance reaches a power of two; the first
        // match is at distance exactly the cycle length.
        SKey sk{(u64)(z % L), (u64)X, (u64)(X >> 64)};
        if (zc >= 0 && sk == ck) {
          int z1 = zc, p = z - z1;
          int i1 = z1 - z0, d = p;
          for (int dd = 1; dd < p; ++dd) {
            if (p % dd) continue;
            bool ok = true;
            for (int j = 0; j < p && ok; ++j) ok = hist[i1 + j] == hist[i1 + (j + dd) % p];
            if (ok) { d = dd; break; }
          }
          return finish(i1, d);
        }
        if (zc < 0 || z - zc == power) { ck = sk; zc = z; power *= 2; }
      }
      u128 m = X;
      // options still in their preperiod are read one by one; an option whose periodic part
      // has started joins the table of its period (see addToGroup)
      for (size_t j = 0; j < pend.size();) {
        int i = pend[j];
        if (z >= os[i]->z1) { addToGroup(i); pend[j] = pend.back(); pend.pop_back(); continue; }
        int o = sc[i][pos[i]];
        if (o >= 0) m |= (u128)1 << o;  // NONE16 and negative offsets never block
        if (++pos[i] == len[i]) pos[i] = wrap[i];
        ++j;
      }
      for (size_t g = 0; g < gp.size(); ++g) {
        m |= gt[g][gph[g]];
        if (++gph[g] == gp[g]) gph[g] = 0;
      }
      for (int cst : consts) if (cst >= z && cst - z < 128) m |= (u128)1 << (cst - z);
      if (~m == 0) return 2;
      u64 lo = (u64)~m, hi = (u64)(~m >> 64);
      int o = lo ? __builtin_ctzll(lo) : 64 + __builtin_ctzll(hi);
      hist.push_back((int16_t)o);
      if (o == 0) { none = true; X = 0; continue; }
      X = (X >> 1) | ((u128)1 << (o - 1));
    }
    return 0;
  }

  TypeIResult typeI(const H& h0, int cIdx) {
    if (PERMEMBER) {
      int H0 = 0;
      for (int i = 1; i < NC; ++i) if (h0[i] != OMEGA) H0 = std::max(H0, (int)h0[i]);
      for (int z = 1; z <= H0; ++z) {
        H g = cut(h0, 0, z);
        if (f(g) == z) return {true, true, z, 0, 0};
      }
      if (const Seq* csq = certify(h0, cIdx)) {
        Seq* sq = const_cast<Seq*>(csq);
        if (sq->scan == INT_MIN) {  // scan the member's own sequence once; later calls reuse it
          int len = sq->off.size(), r = -1;
          for (int z = H0 + 1; z < sq->start + len; ++z) {
            int v = seqValue(*sq, h0, cIdx, z);
            if (v == z) { r = z; break; }
            if (v < 0) break;
          }
          sq->scan = r;
        }
        if (sq->scan >= 0) return {true, true, sq->scan, sq->p, 0};
        return {true, false, -1, sq->p, 0};
      }
    }
    TypeIResult t = typeIRun(h0, cIdx, true);
    if (!t.decided) t = typeIRun(h0, cIdx, false);  // cached periods can make the joint period too long
    return t;
  }

  TypeIResult typeIRun(const H& h0, int cIdx, bool useCache) {
    int H0 = 0;
    for (int i = 1; i < NC; ++i) if (h0[i] != OMEGA) H0 = std::max(H0, (int)h0[i]);
    for (int z = 1; z <= H0; ++z) {
      H g = cut(h0, 0, z);
      if (f(g) == z) return {true, true, z, 0, 0};
    }
    // root already cached?
    {
      auto it = seqCache.find(rawKey(h0));
      if (useCache && it != seqCache.end()) {  // values below the cached start: f directly
        ++seqHits;
        const Seq& sq = it->second;
        int len = sq.off.size();
        for (int z = H0 + 1; z < sq.start + len; ++z) {
          int v = seqValue(sq, h0, cIdx, z);
          if (v == z) return {true, true, z, sq.p, 0};
          if (v < 0) return {true, false, -1, sq.p, 0};
        }
        // beyond the explicit range the offsets repeat; a fixed point would have appeared already
        return {true, false, -1, sq.p, 0};
      }
    }
    std::vector<H> Rs;
    std::unordered_map<Key, int, KH> idx;
    std::vector<std::vector<int>> opts;
    idx.emplace(rawKey(h0), 0);
    Rs.push_back(h0);
    for (size_t q = 0; q < Rs.size(); ++q) {
      H r = Rs[q];
      if (useCache && q > 0 && seqCache.count(rawKey(r))) continue;  // cached: options not needed
      for (int d = 1; d < NC; ++d) {
        if (d == cIdx || r[d] == OMEGA) continue;
        for (int z = 0; z < r[d]; ++z) {
          H g = cut(r, d, z);
          Key k = rawKey(g);
          if (!idx.count(k)) { idx.emplace(k, (int)Rs.size()); Rs.push_back(g); }
        }
      }
    }
    int n = Rs.size();
    std::vector<const Seq*> cached(n, nullptr);
    for (int q = 1; q < n && useCache; ++q) {
      auto it = seqCache.find(rawKey(Rs[q]));
      if (it != seqCache.end()) { cached[q] = &it->second; ++seqHits; }
    }
    opts.assign(n, {});
    for (int q = 0; q < n; ++q) {
      if (cached[q]) continue;
      for (int d = 1; d < NC; ++d) {
        if (d == cIdx || Rs[q][d] == OMEGA) continue;
        for (int z = 0; z < Rs[q][d]; ++z) opts[q].push_back(idx[rawKey(cut(Rs[q], d, z))]);
      }
    }
    std::vector<int> order(n);
    for (int q = 0; q < n; ++q) order[q] = q;
    auto sum = [&](const H& r) { int s = 0; for (int i = 1; i < NC; ++i) if (r[i] != OMEGA) s += r[i]; return s; };
    std::sort(order.begin(), order.end(), [&](int a, int b) { return sum(Rs[a]) < sum(Rs[b]); });
    std::vector<char> none(n, 0);
    std::vector<std::vector<int>> consts(n);
    int maxConst = 0;
    long long L = 1;      // lcm of the periods of the cached sequences used
    int Zc = 0;           // from here on, every cached sequence is in its periodic part
    for (int q = 0; q < n; ++q) {
      if (cached[q]) {
        long long p = cached[q]->p, a = L, b = p;
        while (b) { long long t = a % b; a = b; b = t; }
        L = std::min<long long>(L / a * p, 1000000007LL);
        Zc = std::max(Zc, cached[q]->start + (int)cached[q]->off.size());
        continue;
      }
      H r = Rs[q];
      for (int z = 1; z <= H0 && !none[q]; ++z) {
        H g = r;
        g[cIdx] = (uint8_t)z;
        for (int i = 1; i < NC; ++i) if (i != cIdx && g[i] > z) g[i] = z;
        if (f(g) == z) none[q] = 1;
      }
      for (int z = 0; z <= H0; ++z) {
        H g = r;
        g[cIdx] = (uint8_t)z;
        for (int j : up[cIdx]) if (g[j] > z) g[j] = z;
        uint16_t v = f(g);
        if (v != NONE) { consts[q].push_back(v); maxConst = std::max(maxConst, (int)v); }
      }
    }
    if (L > 2000 || Zc > ZSIM / 2) return {false, false, -1, 0, 0};  // hopeless with the cache
    std::vector<std::vector<int>> X(n);
    std::vector<int> F(n);
    const std::vector<char> none0 = none;
    int fixedZ = -1;
    // one step of the deterministic machine: compute F at z, then update the pending offsets
    auto step = [&](int z, std::vector<std::vector<int16_t>>* hist, bool& overflow) {
      for (int q : order) {
        if (cached[q]) { F[q] = seqValue(*cached[q], Rs[q], cIdx, z); continue; }
        if (none[q]) { F[q] = -1; continue; }
        std::vector<int> ex = X[q];
        for (int r : opts[q]) {
          int fr = cached[r] ? seqValue(*cached[r], Rs[r], cIdx, z) : F[r];
          if (fr >= 0) ex.push_back(fr - z);
        }
        for (int cst : consts[q]) if (cst >= z) ex.push_back(cst - z);
        std::sort(ex.begin(), ex.end());
        int o = 0;
        for (int e : ex) { if (e < o) continue; if (e == o) ++o; else break; }
        F[q] = z + o;
      }
      for (int q = 0; q < n; ++q) {
        if (cached[q]) continue;
        if (hist) {
          int o = none[q] ? NONE16 : F[q] - z;
          if (o > 32767) overflow = true;
          (*hist)[q].push_back((int16_t)o);
        }
        if (none[q]) continue;
        int o = F[q] - z;
        if (o == 0) {
          none[q] = 1;
          if (q == 0 && fixedZ < 0) fixedZ = z;
          X[q].clear();
          continue;
        }
        std::vector<int> nx;
        for (int e : X[q]) if (e >= 1) nx.push_back(e - 1);
        nx.push_back(o - 1);
        std::sort(nx.begin(), nx.end());
        nx.erase(std::unique(nx.begin(), nx.end()), nx.end());
        X[q] = nx;
      }
    };
    // the state: z mod L (phase of the cached sequences), and each simulated member's NONE flag
    // and pending offsets. Kept as a 128-bit hash; a match is then checked exactly by replay.
    auto stateHash = [&](int z) {
      u64 h1 = 0x9E3779B97F4A7C15ull ^ (u64)(z % L), h2 = 0xD1B54A32D192ED03ull + (u64)(z % L);
      auto mix = [&](u64 v) {
        h1 = (h1 ^ v) * 0xBF58476D1CE4E5B9ull; h1 ^= h1 >> 31;
        h2 = (h2 + v + 0x632BE59BD9B4E019ull) * 0x94D049BB133111EBull; h2 ^= h2 >> 29;
      };
      for (int q = 0; q < n; ++q) {
        if (cached[q]) continue;
        mix(none[q] ? 0xFFFFFFFFull : 0xFFFFFFFEull);
        for (int o : X[q]) mix((u64)o);
        mix(0xFFFFFFFDull);
      }
      return Key{h1, h2};
    };
    auto stateStr = [&](int z) {
      std::string st = std::to_string(z % L) + "#";
      for (int q = 0; q < n; ++q) {
        if (cached[q]) continue;
        st.push_back(none[q] ? 'N' : 'L');
        for (int o : X[q]) { st += std::to_string(o); st.push_back(','); }
        st.push_back('|');
      }
      return st;
    };
    std::unordered_map<Key, int, KH> seen;
    bool dummy = false;
    for (int z = H0 + 1; z <= ZSIM; ++z) {
      if (z > maxConst + 1 && z >= Zc) {
        Key hk = stateHash(z);
        auto it = seen.find(hk);
        if (it != seen.end()) {
          int z1 = it->second, p = z - z1;
          // exact check: replay from the start to z1 and compare the full states
          std::string stZ = stateStr(z);
          int fixedSaved = fixedZ;
          for (auto& x : X) x.clear();
          none = none0;
          fixedZ = -1;
          int nsim = 0;
          for (int q = 0; q < n; ++q) if (!cached[q]) ++nsim;
          bool record = (long long)nsim * (z - H0) <= HISTCAP;
          bool overflow = false;
          std::vector<std::vector<int16_t>> hist(record ? n : 0);
          bool match = false;
          for (int zz = H0 + 1; zz < z; ++zz) {
            if (zz == z1) { match = stateStr(zz) == stZ; if (!match) break; }
            step(zz, record ? &hist : nullptr, overflow);
          }
          fixedZ = fixedSaved;
          if (!match) return {false, fixedZ >= 0, fixedZ, 0, (int)seen.size()};  // hash collision
          if (record && !overflow) {
            for (int q = 0; q < n; ++q) {
              if (cached[q]) continue;
              Key k = rawKey(Rs[q]);
              if (seqCache.count(k)) continue;
              // this member's own minimal period d | p and preperiod start i1 (indices into hist)
              const std::vector<int16_t>& hv = hist[q];
              int i1 = z1 - (H0 + 1), d = p;
              for (int dd = 1; dd < p; ++dd) {
                if (p % dd) continue;
                bool ok = true;
                for (int j = 0; j < p && ok; ++j) ok = hv[i1 + j] == hv[i1 + (j + dd) % p];
                if (ok) { d = dd; break; }
              }
              while (i1 > 0 && hv[i1 - 1] == hv[i1 - 1 + d]) --i1;
              seqCache.emplace(k, Seq{H0 + 1, OffVec(std::vector<int16_t>(hv.begin(), hv.begin() + i1 + d), i1),
                                      H0 + 1 + i1, d});
              ++seqStored;
            }
          }
          return {true, fixedZ >= 0, fixedZ, p, (int)seen.size()};
        }
        seen.emplace(hk, z);
      }
      step(z, nullptr, dummy);
    }
    return {false, fixedZ >= 0, fixedZ, 0, (int)seen.size()};
  }

  // Is (omega, r) P? r contains at least one OMEGA. Returns bit1 = P, bit2 = exact.
  uint8_t pw(const H& h, Why* why = nullptr) {
    Key k = key(h);
    if (!why) {
      auto it = wmemo.find(k);
      if (it != wmemo.end()) return it->second;
    }
    ++wcount;
    spend();
    int hf = 0;
    for (int i = 1; i < NC; ++i) if (h[i] != OMEGA) hf = std::max(hf, (int)h[i]);
    int cap = std::min(250, ALPHA * hf + DSLACK);
    uint8_t res = 1;
    bool found = false, exactWin = false;
    int nW = 0, cW = -1;
    for (int i = 1; i < NC; ++i) if (h[i] == OMEGA) { ++nW; cW = i; }
    bool exactP = false;
    bool decided = false;
    if (nW == 1 && EXACT1) {
      TypeIResult t = typeI(h, cW);
      if (t.decided) {
        decided = true;
        ++typeICertified;
        if (t.hasP) { found = true; exactWin = true; if (why) *why = {0, t.z, true}; }
        else exactP = true;
      } else {
        ++typeIUncertified;
      }
    }
    if (!decided) {
      for (int z = 1; z <= cap && !exactWin; ++z) {
        H g = cut(h, 0, z);
        if (f(g) == z) { found = true; exactWin = true; if (why) *why = {0, z, true}; }
      }
    }
    // Moves on the rest that leave omega cells. Two passes: first the options with exactly one
    // omega cell besides the poison (two-wide stalks, decided exactly and quickly), then the rest.
    for (int pass = 0; pass < 2 && !found; ++pass) {
      for (int c = 1; c < NC && !found; ++c) {
        int zmax = h[c] == OMEGA ? cap : h[c] - 1;
        for (int z = 0; z <= zmax && !found; ++z) {
          H g = cut(h, c, z);
          int nWg = 0;
          for (int i = 1; i < NC; ++i) if (g[i] == OMEGA) ++nWg;
          if (!nWg) continue;
          if ((nWg == 1) != (pass == 0)) continue;
          uint8_t r = pw(g);
          if (r & 1) { found = true; exactWin = r & 2; if (why) *why = {c, z, (bool)(r & 2)}; }
          else if (!(r & 2)) exactP = false;
          if (h[c] == OMEGA) exactP = false;
        }
      }
    }
    if (found) res = exactWin ? 2 : 0;
    else if (exactP && nW == 1) res = 3;
    if (!why) wmemo.emplace(k, res);
    return res;
  }

  // Decide any position (finite or with omega). Returns bit1 = P, bit2 = exact.
  uint8_t decide(const H& h) {
    if (h[0] != OMEGA) return (f(h) == h[0]) ? 3 : 2;
    bool anyW = false;
    for (int i = 1; i < NC; ++i) if (h[i] == OMEGA) anyW = true;
    if (!anyW) return 2;  // one infinite column: N
    return pw(h);
  }
};

}  // namespace rod
