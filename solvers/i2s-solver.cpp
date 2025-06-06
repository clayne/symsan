#include "solver.h"

#include "dfsan/dfsan.h"

#include <math.h>
#include <string.h>

using namespace rgd;

#define DEBUG 0

#if !DEBUG
#undef DEBUGF
#define DEBUGF(_str...) do { } while (0)
#elif !defined (DEBUGF)
#define DEBUGF(_str...) do { fprintf(stderr, _str); } while (0)
#endif

#ifndef WARNF
#define WARNF(_str...) do { fprintf(stderr, _str); } while (0)
#endif

#if defined(__GNUC__)
static inline bool (likely)(bool x) { return __builtin_expect((x), true); }
static inline bool (unlikely)(bool x) { return __builtin_expect((x), false); }
#else
static inline bool (likely)(bool x) { return x; }
static inline bool (unlikely)(bool x) { return x; }
#endif

#undef SWAP64
#define SWAP64(_x)                                                             \
  ({                                                                           \
                                                                               \
    uint64_t _ret = (_x);                                                           \
    _ret =                                                                     \
        (_ret & 0x00000000FFFFFFFF) << 32 | (_ret & 0xFFFFFFFF00000000) >> 32; \
    _ret =                                                                     \
        (_ret & 0x0000FFFF0000FFFF) << 16 | (_ret & 0xFFFF0000FFFF0000) >> 16; \
    _ret =                                                                     \
        (_ret & 0x00FF00FF00FF00FF) << 8 | (_ret & 0xFF00FF00FF00FF00) >> 8;   \
    _ret;                                                                      \
                                                                               \
  })

// It is impossible to define 128 bit constants, so ...
#ifdef WORD_SIZE_64
  #define SWAPN(_x, _l)                            \
    ({                                             \
                                                   \
      u128  _res = (_x), _ret;                     \
      char *d = (char *)&_ret, *s = (char *)&_res; \
      int   i;                                     \
      for (i = 0; i < 16; i++)                     \
        d[15 - i] = s[i];                          \
      u32 sr = 128U - ((_l) << 3U);                \
      (_ret >>= sr);                               \
      (u128) _ret;                                 \
                                                   \
    })
#endif

#define SWAPNN(_x, _y, _l)                     \
  ({                                           \
                                               \
    char *d = (char *)(_x), *s = (char *)(_y); \
    u32   i, l = (_l)-1;                       \
    for (i = 0; i <= l; i++)                   \
      d[l - i] = s[i];                         \
                                               \
  })

static uint64_t get_i2s_value(uint32_t comp, uint64_t v, bool rhs) {
  switch (comp) {
    case rgd::Equal:
    case rgd::Ule:
    case rgd::Uge:
    case rgd::Sle:
    case rgd::Sge:
      return v;
    case rgd::Distinct:
    case rgd::Ugt:
    case rgd::Sgt:
      if (rhs) return v - 1;
      else return v + 1;
    case rgd::Ult:
    case rgd::Slt:
      if (rhs) return v + 1;
      else return v - 1;
    default:
      WARNF("Non-relational i2s op %u!\n", comp);
  }
  return v;
}

static inline uint64_t _get_binop_value(uint64_t v1, uint64_t v2, uint16_t kind) {
  switch (kind) {
    case rgd::Add: return v1 + v2;
    case rgd::Sub: return v1 - v2;
    case rgd::Mul: return v1 * v2;
    case rgd::UDiv: return v2 ? v1 / v2 : 0;
    case rgd::SDiv: return v2 ? (int64_t)v1 / (int64_t)v2 : 0;
    case rgd::URem: return v2 ? v1 % v2 : 0;
    case rgd::SRem: return v2 ? (int64_t)v1 % (int64_t)v2 : 0;
    case rgd::And: return v1 & v2;
    case rgd::Or: return v1 | v2;
    case rgd::Xor: return v1 ^ v2;
    case rgd::Shl: return v1 << v2;
    case rgd::LShr: return v1 >> v2;
    case rgd::AShr: return (int64_t)v1 >> v2;
    default: WARNF("Non-binary i2s op %u!\n", kind);
  }
  return 0;
}

static inline uint64_t _get_binop_value_r(uint64_t r, uint64_t const_op, uint16_t kind, bool rhs) {
  // we aim to reverse the binary operation
  // if rhs:              const_op op v = r
  // if lhs (i.e., !rhs): v op const_op = r
  switch (kind) {
    case rgd::Add: return r - const_op; // v = r - const_op
    case rgd::Sub: return rhs ? const_op - r : r + const_op; // rhs: v = const_op - r; lhs: v = r + const_op
    case rgd::Mul: return r / const_op; // v = r / const_op
    case rgd::UDiv: return rhs ? const_op / r : r * const_op; // rhs: v = const_op / r; lhs: v = r * const_op
    case rgd::SDiv: return rhs ? (int64_t)const_op / (int64_t)r : (int64_t)r * (int64_t)const_op;
    case rgd::URem:
      if (rhs) {
        if (const_op < r) {
          WARNF("URem rhs const_op < r\n");
          return r;
        }
        // const_op % v = r
        // if const_op > r, const_op % (const_op - r) = r
        // if const_op == r, const_op % (const_op + 1) = const_op = r
        // if const_op < r, not possible
        return const_op > r ? const_op - r : const_op + 1;
      } else {
        // XXX: (v % const_op) % const_op == v % const_op = r
        return r;
      }
    case rgd::SRem:
      if (rhs) {
        if ((int64_t)const_op < (int64_t)r) {
          WARNF("SRem rhs const_op < r\n");
          return r;
        }
        return (int64_t)const_op > (int64_t)r ? (int64_t)const_op - (int64_t)r : (int64_t)const_op + 1;
      } else {
        return r;
      }
    case rgd::And: return (r & const_op) == r ? r : const_op; // XXX: when r = v & const_op, (r) & const_op = (v & const_op) & const_op = v & const_op = r
    case rgd::Or: return (r | const_op) == r ? r : const_op;  // XXX: (a | b) | b == a | b
    case rgd::Xor: return r ^ const_op; // v = r ^ const_op
    case rgd::Shl:
      if (rhs) {
        if (const_op == 1) {
          double log2 = std::log2(r);
          return static_cast<uint64_t>(log2);
        } else {
          WARNF("unsupported Shl (rhs) const_op %lu\n", const_op);
          return 0;
        }
      } else {
        return r >> const_op; // v = r >> const_op
      }
    case rgd::LShr:
      if (rhs) {
        WARNF("LShr rhs not supported\n");
        return r; // FIXME: r probably is not correct
      }
      return r << const_op; // v = r << diff
    case rgd::AShr:
      if (rhs) {
        WARNF("AShr rhs not supported");
        return r; // FIXME: r probably is not correct
      }
      return (int64_t)r << const_op;
    default: WARNF("Non-binary binop_value op %u!\n", kind);
  }
  return 0;
}

static uint64_t get_binop_value(std::shared_ptr<const Constraint> constraint,
    const AstNode &node, uint64_t value, uint64_t &const_op, bool &rhs) {
  auto &left = node.children(0);
  auto &right = node.children(1);
  uint64_t r = 0;
  if (left.kind() == Constant) {
    const_op = constraint->input_args[left.index()].second;
    r = _get_binop_value(const_op, value, node.kind());
    rhs = true;
  } else if (right.kind() == Constant) {
    const_op = constraint->input_args[right.index()].second;
    r = _get_binop_value(value, const_op, node.kind());
    rhs = false;
  }
  return r;
}

I2SSolver::I2SSolver(): matches(0), mismatches(0) {
  binop_mask.set(rgd::Add);
  binop_mask.set(rgd::Sub);
  binop_mask.set(rgd::Mul);
  binop_mask.set(rgd::UDiv);
  binop_mask.set(rgd::SDiv);
  binop_mask.set(rgd::URem);
  binop_mask.set(rgd::SRem);
  binop_mask.set(rgd::And);
  // binop_mask.set(rgd::Or);
  binop_mask.set(rgd::Xor);
  // binop_mask.set(rgd::Shl);
  binop_mask.set(rgd::LShr);
  binop_mask.set(rgd::AShr);
}

solver_result_t
I2SSolver::solve_icmp(std::shared_ptr<const Constraint> const& c,
                      std::unique_ptr<ConsMeta> const& cm,
                      uint32_t comparison,
                      const uint8_t *in_buf, size_t in_size,
                      uint8_t *out_buf, size_t &out_size) {

  uint64_t value = 0, value_r = 0;
  uint64_t r = 0;
  for (auto const& candidate : cm->i2s_candidates) {
    size_t offset = candidate.first;
    uint32_t bytes = candidate.second;
    if (bytes > 8) {
      // FIXME: support larger int size
      continue;
    }
    auto atoi = c->atoi_info.find(offset);
    if (likely(atoi == c->atoi_info.end())) {
      // size can be not a power of 2
      memcpy(&value, &in_buf[offset], bytes);
      value_r = SWAP64(value) >> (64 - bytes * 8);
      DEBUGF("i2s: try %lu, length %u = 0x%016lx, 0x%016lx, comparison = %d\n",
          offset, bytes, value, value_r, comparison);
      if (c->op1 == value) {
        matches++;
        r = get_i2s_value(comparison, c->op2, false);
      } else if (c->op2 == value) {
        matches++;
        r = get_i2s_value(comparison, c->op1, true);
      } else if (c->op1 == value_r) {
        matches++;
        r = get_i2s_value(comparison, c->op2, false);
        r = SWAP64(r) >> (64 - bytes * 8);
      } else if (c->op2 == value_r) {
        matches++;
        r = get_i2s_value(comparison, c->op1, true);
        r = SWAP64(r) >> (64 - bytes * 8);
      } else if ((binop_mask & c->ops).count() == 1) {
        // try some simple binary operations
        auto &left = c->get_root()->children(0);
        auto &right = c->get_root()->children(1);
        uint64_t const_op = 0;
        uint64_t mask = (1ULL << (bytes * 8)) - 1;
        uint16_t kind = 0;
        // true if the input is on the right hand side of the comparison
        bool rhs = false;
        // true if the input is on the right hand side of the binary operation
        // NOTE, not the right hand side of the comparison
        bool bop_rhs = false;
        // check reverse too
        bool is_reversed = false;
        // check if lhs of the comparison is a simple binary operation with a constant
        if (isBinaryOperation(left.kind())) {
          r = get_binop_value(c, left, value, const_op, bop_rhs);
          r &= mask; // mask the result to avoid overflow
          DEBUGF("i2s: binop (lhs) %lx (%d) %lx = %lx =? %lx\n", value, left.kind(), const_op, r, c->op1);
          if (r == c->op1) {
            // binop result matches op1 of the comparison
            kind = left.kind();
            rhs = false;
          } else {
            // check value_r
            r = get_binop_value(c, left, value_r, const_op, bop_rhs);
            r &= mask; // mask the result to avoid overflow
            DEBUGF("i2s: binop (lhs) %lx (%d) %lx = %lx =? %lx\n", value_r, left.kind(), const_op, r, c->op1);
            if (r == c->op1) {
              kind = left.kind();
              rhs = false;
              is_reversed = true;
            } else {
              const_op = 0;
            }
          }
        }
        if (isBinaryOperation(right.kind())) {
          r = get_binop_value(c, right, value, const_op, bop_rhs);
          r &= mask; // mask the result to avoid overflow
          DEBUGF("i2s: binop (rhs) %lx (%d) %lx = %lx =? %lx\n", value, right.kind(), const_op, r, c->op2);
          if (r == c->op2) {
            // binop result matches op2 of the comparison
            kind = right.kind();
            rhs = true;
          } else {
            // check value_r
            r = get_binop_value(c, right, value_r, const_op, bop_rhs);
            r &= mask; // mask the result to avoid overflow
            DEBUGF("i2s: binop (lhs) %lx (%d) %lx = %lx =? %lx\n", value_r, left.kind(), const_op, r, c->op1);
            if (r == c->op2) {
              kind = right.kind();
              rhs = true;
              is_reversed = true;
            } else {
              const_op = 0;
            }
          }
        }
        if (const_op == 0) {
          continue; // nothing matches next offset
        }
        matches++;
        // get the expected value
        r = get_i2s_value(comparison, rhs ? c->op1 : c->op2, rhs);
        // apply the diff
        r = _get_binop_value_r(r, const_op, kind, bop_rhs);
        r &= mask; // mask the result to avoid overflow
        // reverse the result if necessary
        if (is_reversed) {
          r = SWAP64(r) >> (64 - bytes * 8);
        }
      } else {
        continue; // next offset
      }
      DEBUGF("i2s: %lu = 0x%lx\n", offset, r);
      if (out_size == 0) memcpy(out_buf, in_buf, in_size); // make a copy
      out_size = in_size;
      memcpy(&out_buf[offset], &r, bytes);
      return SOLVER_SAT;
    } else {
      // atoi
      uint32_t base = std::get<1>(atoi->second);
      uint32_t old_len = std::get<2>(atoi->second);
      DEBUGF("i2s: try atoi %lu, base %u, old_len %u\n", offset, base, old_len);
      long num = 0;
      unsigned long unum = 0;
      bool is_signed = false;
      if (old_len > 0) {
        char buf[old_len + 1];
        memcpy(buf, &in_buf[offset], old_len);
        buf[old_len] = 0;
        is_signed = (buf[0] == '-');
        unum = strtoul(buf, NULL, base); // all operands are unsgined in symsan
      }
      if (c->op1 == unum) {
        matches++;
        r = get_i2s_value(comparison, c->op2, false);
      } else if (c->op2 == unum) {
        matches++;
        r = get_i2s_value(comparison, c->op1, true);
      } else {
        continue; // next offset
      }
      DEBUGF("i2s-atoi: %lu = %lx\n", offset, r);
      const char *format = nullptr;
      switch (base) {
        case 2: format = "%lb"; break;
        case 8: format = "%lo"; break;
        case 10: format = is_signed ? "%ld" : "%lu"; break;
        case 16: format = "%lx"; break;
        default: {
          WARNF("unsupported base %d\n", base);
          continue;
        }
      }
      const size_t max_len = 64; // FIXME: make configurable?
      char *saved = nullptr;
      size_t copy_len = in_size - offset - old_len;
      if (out_size == 0) {
        memcpy(out_buf, in_buf, offset);
      } else {
        copy_len = out_size - offset - old_len;
        saved = (char*)malloc(copy_len);
        memcpy(saved, (char*)out_buf + offset + old_len, copy_len);
      }
      // extend size as in cmplog
      size_t num_len;
      if (is_signed) {
        num_len = snprintf((char*)out_buf + offset, max_len, format, (long)r);
      } else {
        num_len = snprintf((char*)out_buf + offset, max_len, format, r);
      }
      if (out_size == 0) {
        memcpy(out_buf + offset + num_len, in_buf + offset + old_len, copy_len);
        out_size = in_size + num_len - old_len;
      } else {
        memcpy((char*)out_buf + offset + num_len, saved, copy_len);
        free(saved);
        out_size += num_len - old_len;
      }
      return SOLVER_SAT;
    }
  }
  return SOLVER_TIMEOUT;
}

solver_result_t
I2SSolver::solve_memcmp(std::shared_ptr<const Constraint> const& c,
                        std::unique_ptr<ConsMeta> const& cm,
                        const uint8_t *in_buf, size_t in_size,
                        uint8_t *out_buf, size_t &out_size) {

  DEBUGF("i2s: try memcmp\n");

  size_t const_index = 0;
  for (auto const& arg : c->input_args) {
    if (!arg.first) break; // first constant arg
    const_index++;
  }
  if (const_index == c->input_args.size()) {
    // FIXME: only do memcmp(const, symbolic)
    mismatches++;
    return SOLVER_TIMEOUT;
  }
  if (cm->i2s_candidates.size() != 1) {
    // FIXME: only support single i2s candidate
    WARNF("only support single i2s candidate\n");
    return SOLVER_TIMEOUT;
  }
  size_t offset = cm->i2s_candidates[0].first;
  uint32_t size = cm->i2s_candidates[0].second;
  if (size != c->local_map.size()) {
    WARNF("input size mismatch\n");
    return SOLVER_TIMEOUT;
  }
  // make a copy of the input if not already
  if (out_size == 0) memcpy(out_buf, in_buf, in_size);
  uint64_t value = 0;
  int i = 0;
  auto &right = c->get_root()->children(1);
  if (likely(right.kind() == rgd::Read)) {
    // the memcmp argument is directly from input
    for (size_t o = offset; o < offset + size; o++) {
      if (i == 0)
        value = c->input_args[const_index].second;
      uint8_t v = ((value >> i) & 0xff);
      out_buf[o] = v;
      DEBUGF("  %lu = %u\n", o, v);
      i += 8;
      if (i == 64) {
        const_index++; // move on to the next 64-bit chunk
        i = 0;
      }
    }
    out_size = in_size;
    return SOLVER_SAT;
  } else {
    // there could be transformations on the input
    auto *info = __dfsan::get_label_info(c->get_root()->label());
    uint64_t sample = info->op2.i;
    uint16_t sample_len = info->size > 8 ? 8 : info->size;
    uint8_t sample_buf[sample_len];
    memcpy(sample_buf, &sample, sample_len);
#if DEBUG
    memcpy(&value, &in_buf[offset], size > 8 ? 8 : size);
    DEBUGF("i2s: memcmp encoded: %016lx => %016lx\n", value, sample);
#endif
    uint8_t encode_val = 0, touppwer = 0, tolower = 0;

    // we only have one sample, so we cannot to reliable guessing purely
    // based on input-output pairs, instead, we leverage the symbolic AST
    // to guide the guessing
    uint16_t kind = 0;
    for (uint16_t i = rgd::Add; i < rgd::Shl; ++i) {
      if (i == rgd::Not || i == rgd::Neg || i == rgd::And || i == rgd::Or)
        continue; // we cannot reverse bitwise And and Or
      if (c->ops.test(i)) {
        if (kind != 0) {
          kind = 0;
          break;
        } else {
          kind = i;
        }
      }
    }
    if (kind != 0) {
      // XXX: always assumes const_op is the rhs?
      encode_val = (uint8_t)_get_binop_value_r(sample_buf[0], in_buf[offset], kind, false);
    } else {
      for (auto i = 0; i < sample_len; ++i) {
        // check simple encoding
        tolower = ((in_buf[offset + i] | 0x20) == sample_buf[i]) ? 1 : 0;
        touppwer = ((in_buf[offset + i] & 0x5f) == sample_buf[i]) ? 1 : 0;
      }
    }

    if (encode_val) {
      DEBUGF("i2s: memcmp try encode val = %02x, op = %d\n", encode_val, kind);
      for (size_t o = offset; o < offset + size; o++) {
        if (i == 0)
          value = c->input_args[const_index].second;
        uint8_t v = ((value >> i) & 0xff);
        out_buf[o] = (uint8_t)_get_binop_value_r(v, encode_val, kind, false);
        DEBUGF("  %lu = %u\n", o, v);
        i += 8;
        if (i == 64) {
          const_index++; // move on to the next 64-bit chunk
          i = 0;
        }
      }
      out_size = in_size;
      return SOLVER_SAT;
    } else if (touppwer) {
      DEBUGF("i2s: memcmp try touppwer\n");
      for (size_t o = offset; o < offset + size; o++) {
        if (i == 0)
          value = c->input_args[const_index].second;
        uint8_t v = ((value >> i) & 0xff);
        out_buf[o] = v | 0x20;
        DEBUGF("  %lu = %u\n", o, v);
        i += 8;
        if (i == 64) {
          const_index++; // move on to the next 64-bit chunk
          i = 0;
        }
      }
      out_size = in_size;
      return SOLVER_SAT;
    } else if (tolower) {
      DEBUGF("i2s: memcmp try tolower\n");
      for (size_t o = offset; o < offset + size; o++) {
        if (i == 0)
          value = c->input_args[const_index].second;
        uint8_t v = ((value >> i) & 0xff);
        out_buf[o] = v & 0x5f;
        DEBUGF("  %lu = %u\n", o, v);
        i += 8;
        if (i == 64) {
          const_index++; // move on to the next 64-bit chunk
          i = 0;
        }
      }
      out_size = in_size;
      return SOLVER_SAT;
    } else {
      return SOLVER_TIMEOUT;
    }
  }
  return SOLVER_TIMEOUT;
}

solver_result_t
I2SSolver::solve(std::shared_ptr<SearchTask> task,
                 const uint8_t *in_buf, size_t in_size,
                 uint8_t *out_buf, size_t &out_size) {

  solver_result_t ret = SOLVER_TIMEOUT;
  size_t n = task->size();
  DEBUGF("i2s: new task with %zu constraints\n", n);
  out_size = 0; // use this to indicate whether a copy has been made
  for (size_t i = 0; i < n; ++i) {
    // iterate through all constraints, hoping the stacked mutations would work,
    // instead of destroying each other
    auto const& c = task->constraints(i);
    auto const& cm = task->consmetas(i);
    auto comparison = task->comparisons(i);
    if (likely(isRelationalKind(comparison))) {
      if (solve_icmp(c, cm, comparison, in_buf, in_size, out_buf, out_size) == SOLVER_SAT) {
        // be optimistic, as long as there's one match, we should try the output
        ret = SOLVER_SAT;
      } else {
        mismatches++;
      }
    } else if (comparison == rgd::Memcmp) {
      if (solve_memcmp(c, cm, in_buf, in_size, out_buf, out_size) == SOLVER_SAT) {
        // be optimistic, as long as there's one match, we should try the output
        ret = SOLVER_SAT;
      } else {
        mismatches++;
      }
    } else if (comparison == rgd::MemcmpN) {
      DEBUGF("i2s: try memcmpN\n");
      // copy the matching bytes
      if (out_size == 0) memcpy(out_buf, in_buf, in_size);
      size_t offset = cm->i2s_candidates[0].first;
      uint32_t size = cm->i2s_candidates[0].second;
      out_buf[offset] = in_buf[offset] + 8;
      out_size = in_size;
      ret = SOLVER_SAT;
    }
  }

  return ret;
}