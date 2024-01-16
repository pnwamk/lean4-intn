#include <lean/lean.h>
#include <cstdint>

// WIP - functions are illustrative of what C definitions
// for this Lean4 representation of Int8 will look like
// internally, but not all are present as of 2024-01-15

// https://en.cppreference.com/w/cpp/header/cstdint

// -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
// -- Int8
// -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

extern "C" LEAN_EXPORT int8_t lean_int8_div(int8_t a, int8_t b) {
  if ((a == 0) || ((a == INT8_MIN) && (b == -1))) {
    return a;
  } else {
    return a / b;
  }
}

extern "C" LEAN_EXPORT int8_t lean_int8_mod(int8_t a, int8_t b) {
  if ((a == 0) || ((a == INT8_MIN) && (b == -1))) {
    return 0;
  } else {
    return a % b;
  }
}

static inline uint8_t lean_int8_dec_lt(int8_t a, int8_t b) { return a < b; }
static inline uint8_t lean_int8_dec_le(int8_t a, int8_t b) { return a <= b; }

static inline int16_t lean_int8_to_int16(int8_t a) { return a; }
static inline int32_t lean_int8_to_int32(int8_t a) { return a; }
static inline int64_t lean_int8_to_int64(int8_t a) { return a; }