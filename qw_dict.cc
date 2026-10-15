// qw_dict.cc — dump a librime compiled dictionary as a UTF-8 word list.
//
//   usage: ./qw_dict qw.table.bin qw.prism.bin <out.txt>
//
// The dictionary (one line per entry, below) is written to the path in argv[3].
//
// Output, one line per entry:
//   {word}\t{space-separated syllables}\t{weight}\n
// where `weight` is the raw (pre-log) frequency of table::Entry::weight:
//   max(0, (long long)(exp((double)ln_weight) + 0.5))
//
// Parses:
//   * qw.table.bin  "Rime::Table/4.0": flat arena of POD structs with
//     self-relative int32 OffsetPtrs; metadata -> syllabary (Array<int32>
//     str_ids) -> HeadIndex[422] -> TrunkIndex lv2/lv3 (16B nodes) ->
//     TailIndex (Array<LongEntry>, 16B) -> Entry{int32 str_id; float ln}
//     arrays and extra_code arrays; final block = embedded marisa-trie image
//     ("We love Marisa.") holding every syllable and word text (key ids).
//   * qw.prism.bin  "Rime::Prism/4.0": Metadata(316B), darts-clone 0.32
//     double-array of spelling keys, SpellingMap (Array<{u32 size;
//     OffsetPtr<SpellingDescriptor>}>) and 16B SpellingDescriptor lists
//     {int32 syllable_id; int32 type|corr<<30; float credibility;
//     OffsetPtr<char> tips}.  Its num_syllables drives the syllabary loop.
//
// marisa image layout (pinned submodule commit 3e87d53, lib/marisa):
//   16B magic; then recursively per trie:
//     louds, terminal_flags, link_flags : BitVector
//     bases : Vector<u8>; extras : FlatVector; tail : Vector<char> + BitVector
//     [next trie if link.num_1s != 0 && tail empty]
//     cache : Vector<Cache{3x u32}> (skipped), u32 num_l1_nodes, u32 config.
//   BitVector : Vector<u64 units>, u32 size, u32 num_1s, Vector<Rank9{3xu32}>,
//               Vector<u32> select0s, Vector<u32> select1s.
//   Vector<T> : u64 byte_size, data, pad to 8.
//
// C++98, standard library only. Error handling omitted deliberately.

#include <algorithm>   // std::reverse
#include <cmath>       // std::exp
#include <cstdio>      // fopen/fread/fwrite/stdout/stderr
#include <cstddef>     // std::ptrdiff_t
#include <cstring>     // std::memcpy, std::strlen
#include <string>
#include <vector>

typedef unsigned char       u8;
typedef unsigned short      u16;
typedef unsigned int        u32;
typedef unsigned long long  u64;
typedef signed int          i32;

// ------------------------------------------------------------------ LE reads --

static inline u32 rd32(const char* p) { u32 v; std::memcpy(&v, p, 4); return v; }
static inline i32 rdi32(const char* p) { i32 v; std::memcpy(&v, p, 4); return v; }
static inline u64 rd64(const char* p) { u64 v; std::memcpy(&v, p, 8); return v; }
static inline float rdf(const char* p) { float v; std::memcpy(&v, p, 4); return v; }

static u64 pad8(u64 n) { return (8 - (n % 8)) % 8; }

// ------------------------------------------------------------------ bit ops --

static u8 PC8[256];                 // popcount of a byte
static u8 SEL8[8][256];             // SEL8[i][x] = bit index of the (i+1)-st 1 in x

static u64 popcnt64(u64 x) {        // SWAR
  x = x - ((x >> 1) & 0x5555555555555555ULL);
  x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
  x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
  return (x * 0x0101010101010101ULL) >> 56;
}

static void init_tables() {
  for (u32 x = 0; x < 256; ++x) {
    for (u32 b = 0; b < 8; ++b) PC8[x] += (u8)((x >> b) & 1);
  }
  for (u32 x = 0; x < 256; ++x) {
    u32 k = 0;
    for (u32 b = 0; b < 8; ++b)
      if ((x >> b) & 1) SEL8[k++][x] = (u8)b;
    for (; k < 8; ++k) SEL8[k][x] = 7;   // never read (caller guarantees i < popcount)
  }
}

// Position of the (i+1)-st set bit (0-based) within `unit`, LSB-first.
static u64 select_bit(u64 i, u64 unit) {
  for (u64 b = 0; b < 8; ++b) {
    u32 byte = (u32)((unit >> (8 * b)) & 0xFF);
    u32 pc = PC8[byte];
    if (i < pc) return 8 * b + SEL8[i][byte];
    i -= pc;
  }
  return 64;                            // unreachable for i < popcount(unit)
}

// ---------------------------------------------------------------- BitVector --

struct BitVector {
  std::vector<u64> units;               // WORD_SIZE == 64
  u64 size;
  u64 num_1s;
  std::vector<u32> abs_, lo_, hi_;      // RankIndex[ (size+511)/512 + 1 ]
  std::vector<u32> sel0_, sel1_;

  BitVector() : size(0), num_1s(0) {}

  void map(const char*& p) {
    u64 total = rd64(p); p += 8;
    u64 n = total / 8;
    units.resize((size_t)n);
    for (u64 i = 0; i < n; ++i) units[(size_t)i] = rd64(p + 8 * i);
    p += total + pad8(total);
    size = rd32(p);
    num_1s = rd32(p + 4);
    p += 8;
    u64 rt = rd64(p); p += 8;
    u64 nr = rt / 12;
    abs_.resize((size_t)nr); lo_.resize((size_t)nr); hi_.resize((size_t)nr);
    for (u64 i = 0; i < nr; ++i) {
      abs_[(size_t)i] = rd32(p + 12 * i);
      lo_[(size_t)i]  = rd32(p + 12 * i + 4);
      hi_[(size_t)i]  = rd32(p + 12 * i + 8);
    }
    p += rt + pad8(rt);
    map_u32_vec(p, sel0_);
    map_u32_vec(p, sel1_);
  }

  bool operator[](u64 i) const {
    return ((units[(size_t)(i >> 6)] >> (i & 63)) & 1) != 0;
  }

  // marisa BitVector::rank1 (64-bit units)
  u64 rank1(u64 i) const {
    size_t rid = (size_t)(i / 512);
    u64 off = abs_[rid];
    switch ((i / 64) % 8) {
      case 1: off += lo_[rid] & 0x7FU; break;
      case 2: off += (lo_[rid] >> 7) & 0xFFU; break;
      case 3: off += (lo_[rid] >> 15) & 0xFFU; break;
      case 4: off += (lo_[rid] >> 23) & 0x1FFU; break;
      case 5: off += hi_[rid] & 0x1FFU; break;
      case 6: off += (hi_[rid] >> 9) & 0x1FFU; break;
      case 7: off += (hi_[rid] >> 18) & 0x1FFU; break;
    }
    off += popcnt64(units[(size_t)(i >> 6)] & ((1ULL << (i & 63)) - 1));
    return off;
  }

  // marisa BitVector::select1 (64-bit units)
  u64 select1(u64 i) const {
    u64 sid = i / 512;
    if ((i % 512) == 0) return sel1_[(size_t)sid];
    u64 begin = sel1_[(size_t)sid] / 512;
    u64 end = (sel1_[(size_t)(sid + 1)] + 511) / 512;
    if (begin + 10 >= end) {
      while (i >= abs_[(size_t)(begin + 1)]) ++begin;
    } else {
      while (begin + 1 < end) {
        u64 middle = (begin + end) / 2;
        if (i < abs_[(size_t)middle]) end = middle; else begin = middle;
      }
    }
    size_t rid = (size_t)begin;
    u64 r = i - abs_[rid];
    u64 unit_id = rid * 8;
    u64 rl1 = lo_[rid] & 0x7FU;
    u64 rl2 = (lo_[rid] >> 7) & 0xFFU;
    u64 rl3 = (lo_[rid] >> 15) & 0xFFU;
    u64 rl4 = (lo_[rid] >> 23) & 0x1FFU;
    u64 rl5 = hi_[rid] & 0x1FFU;
    u64 rl6 = (hi_[rid] >> 9) & 0x1FFU;
    u64 rl7 = (hi_[rid] >> 18) & 0x1FFU;
    if (r < rl4) {
      if (r < rl2) {
        if (r >= rl1) { unit_id += 1; r -= rl1; }
      } else if (r < rl3) { unit_id += 2; r -= rl2; }
      else { unit_id += 3; r -= rl3; }
    } else if (r < rl6) {
      if (r < rl5) { unit_id += 4; r -= rl4; }
      else { unit_id += 5; r -= rl5; }
    } else if (r < rl7) { unit_id += 6; r -= rl6; }
    else { unit_id += 7; r -= rl7; }
    return unit_id * 64 + select_bit(r, units[(size_t)unit_id]);
  }

 private:
  static void map_u32_vec(const char*& p, std::vector<u32>& v) {
    u64 total = rd64(p); p += 8;
    u64 n = total / 4;
    v.resize((size_t)n);
    for (u64 i = 0; i < n; ++i) v[(size_t)i] = rd32(p + 4 * i);
    p += total + pad8(total);
  }
};

// --------------------------------------------------------------- FlatVector --

struct FlatVector {
  std::vector<u64> units;
  u64 value_size, size;
  u32 mask;

  FlatVector() : value_size(0), size(0), mask(0) {}

  void map(const char*& p) {
    u64 total = rd64(p); p += 8;
    u64 n = total / 8;
    units.resize((size_t)n);
    for (u64 i = 0; i < n; ++i) units[(size_t)i] = rd64(p + 8 * i);
    p += total + pad8(total);
    value_size = rd32(p); p += 4;
    mask = rd32(p); p += 4;
    size = rd64(p); p += 8;
  }

  u32 operator[](u64 i) const {
    u64 pos = i * value_size;
    u64 unit_id = pos >> 6, off = pos & 63;
    u32 v;
    if (off + value_size <= 64) {
      v = (u32)(units[(size_t)unit_id] >> off);
    } else {
      v = (u32)((units[(size_t)unit_id] >> off) |
                (units[(size_t)(unit_id + 1)] << (64 - off)));
    }
    return v & mask;
  }
};

// ---------------------------------------------------------------- LoudsTrie --

struct LoudsTrie {
  BitVector louds_, tflags_, lflags_;
  const char* bases_;                    // Vector<u8> data
  u64 bases_size_;
  FlatVector extras_;
  const char* tail_buf_;                 // tail::buf_ (Vector<char> data)
  u64 tail_buf_size_;
  BitVector end_flags_;
  LoudsTrie* next_;
  u64 num_l1_nodes_;

  LoudsTrie() : bases_(0), bases_size_(0), tail_buf_(0), tail_buf_size_(0),
                next_(0), num_l1_nodes_(0) {}

  void map(const char*& p) {
    louds_.map(p);
    tflags_.map(p);
    lflags_.map(p);
    u64 bt = rd64(p); p += 8;
    bases_ = p; bases_size_ = bt;
    p += bt + pad8(bt);
    extras_.map(p);
    u64 tt = rd64(p); p += 8;
    tail_buf_ = p; tail_buf_size_ = tt;
    p += tt + pad8(tt);
    end_flags_.map(p);
    if (lflags_.num_1s != 0 && tail_buf_size_ == 0) {   // chained suffix trie
      next_ = new LoudsTrie();
      next_->map(p);
    }
    u64 ct = rd64(p); p += 8;                            // cache_ (skipped)
    p += ct + pad8(ct);
    num_l1_nodes_ = rd32(p); p += 4;
    p += 4;                                              // config_ flags
  }

  u64 get_link(u64 node_id) const {
    return (u64)(u8)bases_[node_id] +
           (u64)extras_[lflags_.rank1(node_id)] * 256;
  }

  void reverse_lookup(u64 key_id, std::string& out) const {
    out.clear();
    u64 node = tflags_.select1(key_id);
    if (node == 0) return;                               // the empty key
    for (;;) {
      if (lflags_[node]) {
        size_t prev = out.size();
        restore(get_link(node), out);
        std::reverse(out.begin() + (std::ptrdiff_t)prev, out.end());
      } else {
        out.push_back(bases_[node]);
      }
      if (node <= num_l1_nodes_) { std::reverse(out.begin(), out.end()); return; }
      node = louds_.select1(node) - node - 1;
    }
  }

  void restore(u64 link, std::string& kb) const {       // append, reversed
    if (next_ != 0) { next_->restore_(link, kb); return; }
    if (end_flags_.size == 0) {                         // MARISA_TEXT_TAIL
      for (const char* q = tail_buf_ + link; *q != '\0'; ++q) kb.push_back(*q);
    } else {                                            // MARISA_BINARY_TAIL
      u64 off = link;
      do { kb.push_back(tail_buf_[off]); } while (!end_flags_[off++]);
    }
  }

  void restore_(u64 node, std::string& kb) const {      // walk up this trie
    for (;;) {
      if (lflags_.operator[](node)) restore(get_link(node), kb);
      else kb.push_back(bases_[node]);
      if (node <= num_l1_nodes_) return;
      node = louds_.select1(node) - node - 1;
    }
  }
};

// ------------------------------------------------------------------- output --

struct Out {
  enum { kBufSize = 1 << 22 };
  char* buf;                          // dynamically allocated output buffer
  size_t n;
  std::FILE* f;
  Out() : buf(new char[kBufSize]), n(0), f(0) {}
  ~Out() { flush(); if (f) std::fclose(f); delete[] buf; }
  void flush() { if (n) { fwrite(buf, 1, n, f); n = 0; } }
  void str(const char* p, size_t k) {
    if (n + k > kBufSize) { flush(); }
    if (k > kBufSize) { fwrite(p, 1, k, f); return; }
    std::memcpy(buf + n, p, k); n += k;
  }
  void ch(char c) { if (n == kBufSize) flush(); buf[n++] = c; }
  void u64v(u64 v) {
    char t[24]; int k = 0;
    do { t[k++] = (char)('0' + (v % 10)); v /= 10; } while (v);
    while (k) ch(t[--k]);
  }
};

// -------------------------------------------------------------------- prism --

static u32 d_offset(u32 u) { return (u >> 10) << ((u & (1u << 9)) >> 6); }
static u32 d_label(u32 u)  { return u & 0xFFu; }
static u32 d_is_leaf(u32 u){ return (u >> 31) & 1u; }
static u32 d_has_leaf(u32 u){ return (u >> 8) & 1u; }

struct PrismInfo {
  u32 num_syllables;
  u32 num_spellings;
  u32 dict_checksum;
  u32 schema_checksum;
  u32 recovered_keys;
  u32 descriptor_total;
  u32 max_syllable_id;

  PrismInfo() : num_syllables(0), num_spellings(0), dict_checksum(0),
                schema_checksum(0), recovered_keys(0), descriptor_total(0),
                max_syllable_id(0) {}
};

static void parse_prism(const char* b, PrismInfo& pi) {
  // table::prism::Metadata, 316 bytes
  pi.dict_checksum   = rd32(b + 32);
  pi.schema_checksum = rd32(b + 36);
  pi.num_syllables   = rd32(b + 40);
  pi.num_spellings   = rd32(b + 44);
  u32 da_size        = rd32(b + 48);
  i32 da_delta       = rdi32(b + 52);  u64 da_off = da_delta ? 52u + (u64)da_delta : 0;
  i32 sm_delta       = rdi32(b + 56);  u64 sm_off = sm_delta ? 56u + (u64)sm_delta : 0;

  std::vector<u32> units(da_size);
  for (u32 i = 0; i < da_size; ++i) units[i] = rd32(b + da_off + 4u * i);

  // DFS over the darts-clone double array -> (spelling, spelling_id)
  std::vector<char> seen(da_size, 0);
  std::vector<std::pair<u32, std::string> > stack;
  stack.push_back(std::make_pair((u32)0, std::string()));
  while (!stack.empty()) {
    u32 pos = stack.back().first;
    std::string key = stack.back().second;
    stack.pop_back();
    if (pos >= da_size || seen[pos]) continue;
    seen[pos] = 1;
    u32 u = units[pos];
    u32 base = d_offset(u);
    if (d_has_leaf(u)) {
      u32 leaf = pos ^ base;
      if (leaf < da_size && d_is_leaf(units[leaf])) ++pi.recovered_keys;
    }
    for (u32 c = 1; c < 256; ++c) {
      u32 child = pos ^ base ^ c;
      if (child < da_size && d_label(units[child]) == c && !d_is_leaf(units[child]))
        stack.push_back(std::make_pair(child, key + (char)c));
    }
  }

  // SpellingMap = Array<{u32 size; OffsetPtr<SpellingDescriptor> at}>
  u32 map_size = rd32(b + sm_off);
  for (u32 i = 0; i < map_size; ++i) {
    u64 item = sm_off + 4u + 8u * i;
    u32 n = rd32(b + item);
    i32 d = rdi32(b + item + 4);
    if (n == 0 || d == 0) continue;
    u64 dlist = item + 4u + (u64)d;
    pi.descriptor_total += n;
    for (u32 j = 0; j < n; ++j) {
      u64 e = dlist + 16u * j;
      u32 syl = rd32(b + e);            // int32 syllable_id
      if (syl > pi.max_syllable_id) pi.max_syllable_id = syl;
      // e+4: type (low 30 bits) | correction (bit 30); e+8: credibility;
      // e+12: OffsetPtr tips — parsed per the spec, values not needed for dump.
    }
  }
}

// --------------------------------------------------------------------- main --

static std::vector<char> read_file(const char* path) {
  std::FILE* f = std::fopen(path, "rb");
  std::fseek(f, 0, SEEK_END);
  u64 sz = (u64)std::ftell(f);
  std::fseek(f, 0, SEEK_SET);
  std::vector<char> v((size_t)sz);
  size_t got = std::fread(&v[0], 1, (size_t)sz, f);
  (void)got;
  std::fclose(f);
  return v;
}

int main(int, char** argv) {
  init_tables();

  const char* table_path = argv[1];
  const char* prism_path = argv[2];

  Out out;
  out.f = std::fopen(argv[3], "wb");      // dictionary output goes to argv[3]

  std::vector<char> tbl = read_file(table_path);
  std::vector<char> prm = read_file(prism_path);
  const char* T = &tbl[0];
  const char* P = &prm[0];

  // ---- prism ----
  PrismInfo pi;
  parse_prism(P, pi);

  // ---- table::Metadata (68 B) ----
  u32 table_cksum  = rd32(T + 32);
  u32 num_syll     = rd32(T + 36);
  u32 num_entries  = rd32(T + 40);
  u64 sylabary_at  = 44u + (u32)rdi32(T + 44);
  u64 index_at     = 48u + (u32)rdi32(T + 48);
  u64 image_at     = 60u + (u32)rdi32(T + 60);
  u32 image_size   = rd32(T + 64);
  (void)num_syll;

  // ---- marisa string table ----
  LoudsTrie trie;
  const char* q = T + image_at;
  q += 16;                                       // "We love Marisa." header
  trie.map(q);                                   // chained tries consumed recursively

  // ---- syllabary: Array<int32 str_id> ----
  u32 syl_n = rd32(T + sylabary_at);             // == prism.num_syllables
  std::vector<std::string> syl_text(syl_n);
  for (u32 i = 0; i < syl_n; ++i) {
    i32 sid = rdi32(T + sylabary_at + 4u + 4u * i);
    trie.reverse_lookup((u64)(u32)sid, syl_text[i]);
  }

  // ---- index DFS: HeadIndex -> TrunkIndex lv2 -> lv3 -> TailIndex ----
  u32 head_n = rd32(T + index_at);
  u64 head_at = index_at + 4u;                   // HeadIndexNode[head_n], 12 B
  u64 emitted = 0;

  for (u64 s0 = 0; s0 < head_n; ++s0) {
    u64 hb = head_at + 12u * s0;
    u32 en = rd32(T + hb);
    i32 ed = rdi32(T + hb + 4);
    if (en && ed) {                              // 1-syllable entries
      u64 ea = (hb + 4u) + (u64)ed;
      for (u32 k = 0; k < en; ++k) {
        i32 sid = rdi32(T + ea + 8u * k);
        float w = rdf(T + ea + 8u * k + 4);
        std::string word;
        trie.reverse_lookup((u64)(u32)sid, word);
        out.str(word.data(), word.size());
        out.ch('\t');
        out.str(syl_text[(size_t)s0].c_str(), syl_text[(size_t)s0].size());
        out.ch('\t');
        long long rw = (long long)(std::exp((double)w) + 0.5);
        if (rw < 0) rw = 0;
        out.u64v((u64)rw);
        out.ch('\n');
        ++emitted;
      }
    }
    i32 nd = rdi32(T + hb + 8);
    if (!nd) continue;
    u64 lv2 = (hb + 8u) + (u64)nd;               // TrunkIndexNode[], 16 B
    u32 n2 = rd32(T + lv2);
    u64 lv2_at = lv2 + 4u;
    for (u32 j2 = 0; j2 < n2; ++j2) {
      u64 b2 = lv2_at + 16u * j2;
      u32 key2 = rd32(T + b2);
      u32 en2 = rd32(T + b2 + 4);
      i32 ed2 = rdi32(T + b2 + 8);
      if (en2 && ed2) {                          // 2-syllable entries
        u64 ea = (b2 + 8u) + (u64)ed2;
        for (u32 k = 0; k < en2; ++k) {
          i32 sid = rdi32(T + ea + 8u * k);
          float w = rdf(T + ea + 8u * k + 4);
          std::string word;
          trie.reverse_lookup((u64)(u32)sid, word);
          out.str(word.data(), word.size());
          out.ch('\t');
          out.str(syl_text[(size_t)s0].c_str(), syl_text[(size_t)s0].size());
          out.ch(' ');
          out.str(syl_text[(size_t)key2].c_str(), syl_text[(size_t)key2].size());
          out.ch('\t');
          long long rw = (long long)(std::exp((double)w) + 0.5);
          if (rw < 0) rw = 0;
          out.u64v((u64)rw);
          out.ch('\n');
          ++emitted;
        }
      }
      i32 nd2 = rdi32(T + b2 + 12);
      if (!nd2) continue;
      u64 lv3 = (b2 + 12u) + (u64)nd2;
      u32 n3 = rd32(T + lv3);
      u64 lv3_at = lv3 + 4u;
      for (u32 j3 = 0; j3 < n3; ++j3) {
        u64 b3 = lv3_at + 16u * j3;
        u32 key3 = rd32(T + b3);
        u32 en3 = rd32(T + b3 + 4);
        i32 ed3 = rdi32(T + b3 + 8);
        if (en3 && ed3) {                        // 3-syllable entries
          u64 ea = (b3 + 8u) + (u64)ed3;
          for (u32 k = 0; k < en3; ++k) {
            i32 sid = rdi32(T + ea + 8u * k);
            float w = rdf(T + ea + 8u * k + 4);
            std::string word;
            trie.reverse_lookup((u64)(u32)sid, word);
            out.str(word.data(), word.size());
            out.ch('\t');
            out.str(syl_text[(size_t)s0].c_str(), syl_text[(size_t)s0].size());
            out.ch(' ');
            out.str(syl_text[(size_t)key2].c_str(), syl_text[(size_t)key2].size());
            out.ch(' ');
            out.str(syl_text[(size_t)key3].c_str(), syl_text[(size_t)key3].size());
            out.ch('\t');
            long long rw = (long long)(std::exp((double)w) + 0.5);
            if (rw < 0) rw = 0;
            out.u64v((u64)rw);
            out.ch('\n');
            ++emitted;
          }
        }
        i32 nd3 = rdi32(T + b3 + 12);
        if (!nd3) continue;
        u64 tail = (b3 + 12u) + (u64)nd3;        // TailIndex: Array<LongEntry>
        u32 nt = rd32(T + tail);
        u64 tail_at = tail + 4u;
        for (u32 jt = 0; jt < nt; ++jt) {        // >=4-syllable entries
          u64 lb = tail_at + 16u * jt;
          u32 xn = rd32(T + lb);
          i32 xd = rdi32(T + lb + 4);
          u64 xcode = (lb + 4u) + (u64)(xd != 0 ? xd : 0);
          i32 sid = rdi32(T + lb + 8);
          float w = rdf(T + lb + 12);
          std::string word;
          trie.reverse_lookup((u64)(u32)sid, word);
          out.str(word.data(), word.size());
          out.ch('\t');
          out.str(syl_text[(size_t)s0].c_str(), syl_text[(size_t)s0].size());
          out.ch(' ');
          out.str(syl_text[(size_t)key2].c_str(), syl_text[(size_t)key2].size());
          out.ch(' ');
          out.str(syl_text[(size_t)key3].c_str(), syl_text[(size_t)key3].size());
          if (xn && xd) {
            for (u32 m = 0; m < xn; ++m) {
              u32 extra = rd32(T + xcode + 4u * m);
              out.ch(' ');
              out.str(syl_text[(size_t)extra].c_str(),
                      syl_text[(size_t)extra].size());
            }
          }
          out.ch('\t');
          long long rw = (long long)(std::exp((double)w) + 0.5);
          if (rw < 0) rw = 0;
          out.u64v((u64)rw);
          out.ch('\n');
          ++emitted;
        }
      }
    }
  }
  out.flush();

  std::fprintf(stderr,
      "table: %u syllables (prism: %u), %u entries, emitted %u; "
      "marisa image %u B, %u keys; cksum table 0x%08x / prism 0x%08x, "
      "prism: %u/%u spellings in double array, %u descriptors\n",
      syl_n, pi.num_syllables, num_entries, (u32)emitted, image_size,
      (u32)trie.tflags_.num_1s, table_cksum, pi.dict_checksum,
      pi.recovered_keys, pi.num_spellings, pi.descriptor_total);
  return (emitted == num_entries) ? 0 : 1;
}
