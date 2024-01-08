#include <lean/lean.h>
#include <limits>

// -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
// -- Int8
// -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

extern "C" LEAN_EXPORT uint8_t lean_int8_div(uint8_t a, uint8_t b) {
  if ((a == 0) || ((a == numeric_limits<int8_t>::min()) && (b == ((uint8_t)((int8_t)-1))))) {
    return a;
  } else {
    return ((int8_t) a) / ((int8_t) b);
  }
}

extern "C" LEAN_EXPORT uint8_t lean_int8_mod(uint8_t a, uint8_t b) {
  if ((a == 0) || ((a == int8_t_min) && (b == ((uint8_t)((int8_t)-1))))) {
    return 0;
  } else {
    return ((int8_t) a) % ((int8_t) b);
  }
}

static inline uint8_t lean_int8_dec_lt(uint8_t a, uint8_t b) { return a < b}
static inline uint8_t lean_int8_dec_le(uint8_t a, uint8_t b) { return a <= b}

static inline uint16_t lean_int8_to_int16(uint8_t a) { return (uint16_t)((int16_t)((int8_t)a)) }
static inline uint32_t lean_int8_to_int32(uint8_t a) { return (uint32_t)((int32_t)((int8_t)a)) }
static inline uint64_t lean_int8_to_int64(uint8_t a) { return (uint64_t)((int64_t)((int8_t)a)) }
