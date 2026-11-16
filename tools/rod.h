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
#include <climits>
#include <cstdint>
#include <cstdio>
#include <string>
#include <unordered_map>
#include <vector>

namespace rod {

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
  struct Seq { int start; std::vector<int16_t> off; int z1, p; };
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
  const Seq* certify(const H& r, int cIdx) {
    Key k = rawKey(r);
    auto it = seqCache.find(k);
    if (it != seqCache.end()) return &it->second;
    if (memberFail.count(k)) return nullptr;
    spend();
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
    std::vector<int> X;
    std::vector<int16_t> hist;  // offsets F(z) - z for z = H0+1, ...
    std::unordered_map<std::string, int> seen;
    if (L <= ZSIM) {
      for (int z = H0 + 1; z <= ZSIM; ++z) {
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
            return &seqCache.emplace(k, Seq{H0 + 1, hist, H0 + 1 + i1, d}).first->second;
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
    ++memberFailed;
    memberFail.emplace(k, 1);
    return nullptr;
  }

  TypeIResult typeI(const H& h0, int cIdx) {
    if (PERMEMBER) {
      int H0 = 0;
      for (int i = 1; i < NC; ++i) if (h0[i] != OMEGA) H0 = std::max(H0, (int)h0[i]);
      for (int z = 1; z <= H0; ++z) {
        H g = cut(h0, 0, z);
        if (f(g) == z) return {true, true, z, 0, 0};
      }
      if (const Seq* sq = certify(h0, cIdx)) {
        int len = sq->off.size();
        for (int z = H0 + 1; z < sq->start + len; ++z) {
          int v = seqValue(*sq, h0, cIdx, z);
          if (v == z) return {true, true, z, sq->p, 0};
          if (v < 0) return {true, false, -1, sq->p, 0};
        }
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
              seqCache.emplace(k, Seq{H0 + 1, std::vector<int16_t>(hv.begin(), hv.begin() + i1 + d),
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
