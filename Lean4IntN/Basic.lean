import Init.Data.UInt.Log2

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Int8
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

/--
The type of signed 8-bit two's compliment integers. This type is
defined to use a UInt8 representation to make it actually 8 bits
rather than wrapping an `Int`.
-/
structure Int8 where
  ofUInt8 ::
  toUInt8 : UInt8
  deriving DecidableEq, Inhabited, Hashable

/-- The size of type `Int8`, that is, `2^8 = 256`. -/
def Int8.size : Nat := UInt8.size
/-- The max value of type `Int8`, that is, `2^7 - 1 = 127`. -/
def Int8.maxValue : Int8 := ⟨UInt8.ofNat (UInt8.size / 2 - 1)⟩
/-- The smallest value of type `Int8`, that is, `-2^7 = -128`. -/
def Int8.minValue : Int8 := ⟨UInt8.ofNat (UInt8.size / 2)⟩
/-- Return `a` as an `Int8`. Values outside
the `Int8` range will wrap around to a corresponding value
within the range, i.e. `Int8.ofUInt8 <| UInt8.ofNat a`. -/
def Int8.ofNat (a : Nat) : Int8 := ⟨UInt8.ofNat a⟩
instance : OfNat Int8 n := ⟨Int8.ofNat n⟩
/-- Returns `true` if the Int8 `a` is negative. -/
def Int8.isNeg (a : Int8) : Bool := a.toUInt8 > Int8.maxValue.toUInt8
/-- Equivalent to `Int8.ofNat`. -/
abbrev Nat.toInt8 := Int8.ofNat
/-- Returns the bitwise complement of the two's compliment value `a`. -/
def Int8.complement (a : Int8) : Int8 := ⟨a.toUInt8.complement⟩
instance : Complement Int8 := ⟨Int8.complement⟩

/-- Turns an Int8 into a natural number, negative numbers become
  `0`.

  ```
  #eval (7 : Int8).toNat -- 7
  #eval (0 : Int8).toNat -- 0
  #eval (-7 : Int8).toNat -- 0
  ```
-/
def Int8.toNat (a : Int8) : Nat :=
  if a.isNeg
  then 0
  else a.toUInt8.toNat

/-- Return `a` as a `Int8`. Values outside
the `Int8` range will wrap around to a corresponding value
within the range. E.g. `Int8.ofUInt8 <| UInt8.ofNat <| Int.toNat a`
for nonnegative integers. -/
def Int8.ofInt (a : Int) : Int8 :=
  match a with
  | Int.ofNat n => .ofNat n
  | Int.negSucc n => ~~~.ofNat n

/-- Return `a` as an unbound `Int`. -/
def Int8.toInt (a : Int8) : Int :=
  if a.isNeg
  then Int.negOfNat (Int8.size - a.toUInt8.toNat)
  else Int.ofNat a.toUInt8.toNat

instance : ToString Int8 := ⟨fun i => toString i.toInt⟩

/-- Returns the two's compliment negation of `a`. -/
def Int8.neg (a : Int8) : Int8 := ⟨0 - a.toUInt8⟩
instance : Neg Int8 := ⟨Int8.neg⟩

/-- Returns the absolute value of `a` as an unsigned
integer of the same bit width. -/
def Int8.unsignedAbs (a : Int8) : UInt8 :=
  if a.isNeg
  then 0 - a.toUInt8
  else a.toUInt8

/-- Returns the absolute value of `a`.

Note that `Int8.minValue.abs == Int8.minValue` due
to the two's compliment representation.
-/
def Int8.abs (a : Int8) : Int8 := ⟨a.unsignedAbs⟩

/-- Returns `a + b` per two's compliment arithmetic. -/
def Int8.add (a b : Int8) : Int8 := ⟨UInt8.add a.toUInt8 b.toUInt8⟩
instance : Add Int8 := ⟨Int8.add⟩

/-- Returns `a - b` per two's compliment arithmetic. -/
def Int8.sub (a b : Int8) : Int8 := ⟨UInt8.sub a.toUInt8 b.toUInt8⟩
instance : Sub Int8 := ⟨Int8.sub⟩

/-- Returns `a * b` per two's compliment arithmetic. -/
def Int8.mul (a b : Int8) : Int8 := ⟨UInt8.mul a.toUInt8 b.toUInt8⟩
instance : Mul Int8 := ⟨Int8.mul⟩

/-- Returns `a / b` per two's compliment arithmetic. -/
-- @[extern "lean_int8_div"]
def Int8.div (a b : Int8) : Int8 :=
  match a.isNeg, b.isNeg with
  | true,  true => ⟨(-a).toUInt8 / (-b).toUInt8⟩
  | true,  false => -⟨(-a).toUInt8 / b.toUInt8⟩
  | false, true => -⟨a.toUInt8 / (-b).toUInt8⟩
  | false, false => ⟨a.toUInt8 / b.toUInt8⟩
instance : Div Int8 := ⟨Int8.div⟩

/-- Returns `a % b` per two's compliment arithmetic. -/
-- @[extern "lean_int8_mod"]
def Int8.mod (a b : Int8) : Int8 :=
  match a.isNeg, b.isNeg with
  | true,  true => -⟨(-a).toUInt8 % (-b).toUInt8⟩
  | true,  false => -⟨(-a).toUInt8 % b.toUInt8⟩
  | false, true => ⟨a.toUInt8 % (-b).toUInt8⟩
  | false, false => ⟨a.toUInt8 % b.toUInt8⟩
instance : Mod Int8 := ⟨Int8.mod⟩

/-- Returns the bitwise AND of the arguments. -/
def Int8.land (a b : Int8) : Int8 := ⟨UInt8.land a.toUInt8 b.toUInt8⟩
instance : AndOp Int8 := ⟨Int8.land⟩

/-- Returns the bitwise OR of the arguments. -/
def Int8.lor (a b : Int8) : Int8 := ⟨UInt8.lor a.toUInt8 b.toUInt8⟩
instance : OrOp Int8 := ⟨Int8.lor⟩

/-- Returns the bitwise XOR of the arguments. -/
def Int8.xor (a b : Int8) : Int8 := ⟨UInt8.xor a.toUInt8 b.toUInt8⟩
instance : Xor Int8 := ⟨Int8.xor⟩

/-- Returns `a` bitwise left shifted by `b` bits. -/
def Int8.shiftLeft (a b : Int8) : Int8 := ⟨UInt8.shiftLeft a.toUInt8 b.toUInt8⟩
instance : ShiftLeft Int8 := ⟨Int8.shiftLeft⟩

/-- Returns `a` bitwise right shifted by `b` bits. The sign of the result
matches the sign of `a`.-/
def Int8.shiftRight (a b : Int8) : Int8 :=
  if a.isNeg
  then -⟨UInt8.shiftRight (-a).toUInt8 b.toUInt8⟩
  else ⟨UInt8.shiftRight a.toUInt8 b.toUInt8⟩
instance : ShiftRight Int8 := ⟨Int8.shiftRight⟩

/-- `a` is less than `b`.-/
def Int8.lt (a b : Int8) : Prop := a.toInt < b.toInt
instance : LT Int8 := ⟨Int8.lt⟩

/-- `a` is less than or equal to `b`.-/
def Int8.le (a b : Int8) : Prop := a.toInt ≤ b.toInt
instance : LE Int8 := ⟨Int8.le⟩

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_lt"]
def Int8.decLt (a b : Int8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toInt < b.toInt))
instance (a b : Int8) : Decidable (a < b) := Int8.decLt a b

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_le"]
def Int8.decLe (a b : Int8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toInt ≤ b.toInt))
instance (a b : Int8) : Decidable (a ≤ b) := Int8.decLe a b

instance : Max Int8 := maxOfLe
instance : Min Int8 := minOfLe

/-- Returns the log base 2 of `a` for `a ≥ 0`. -/
def Int8.log2 (a : Int8) : Int8 := ⟨UInt8.log2 a.toUInt8⟩


-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Int16
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

/--
The type of signed 16-bit two's compliment integers. This type is
defined to use a UInt16 representation to make it actually 16 bits
rather than wrapping an `Int`.
-/
structure Int16 where
  ofUInt16 ::
  toUInt16 : UInt16
  deriving DecidableEq, Inhabited, Hashable

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Int32
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

/--
The type of signed 32-bit two's compliment integers. This type is
defined to use a UInt32 representation to make it actually 32 bits
rather than wrapping an `Int`.
-/
structure Int32 where
  ofUInt32 ::
  toUInt32 : UInt32
  deriving DecidableEq, Inhabited, Hashable

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Int64
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --

/--
The type of signed 64-bit two's compliment integers. This type is
defined to use a UInt64 representation to make it actually 64 bits
rather than wrapping an `Int`.
-/
structure Int64 where
  ofUInt64 ::
  toUInt64 : UInt64
  deriving DecidableEq, Inhabited, Hashable

-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- IntN coercions
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --


-- @[extern "lean_int8_to_int16"]
-- def Int8.toInt16 (a : Int8) : Int16 := a.toNat.toInt16
-- @[extern "lean_int8_to_int32"]
-- def Int8.toInt32 (a : Int8) : Int32 := a.toNat.toInt32
-- @[extern "lean_int8_to_int64"]
-- def Int8.toInt64 (a : Int8) : Int64 := a.toNat.toInt64
