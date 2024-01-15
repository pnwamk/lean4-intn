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
/-- Equivalent to `Int8.ofNat`. -/
abbrev Nat.toInt8 := Int8.ofNat
/-- Returns `true` if the Int8 `a` is negative. -/
def Int8.isNeg (a : Int8) : Bool := a.toUInt8 > Int8.maxValue.toUInt8
/-- Returns the bitwise complement of the two's compliment value `a`. -/
def Int8.complement (a : Int8) : Int8 := ⟨a.toUInt8.complement⟩
instance : Complement Int8 := ⟨Int8.complement⟩
/-- Returns the two's compliment negation of `a`. -/
def Int8.neg (a : Int8) : Int8 := ⟨0 - a.toUInt8⟩
instance : Neg Int8 := ⟨Int8.neg⟩

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

/-- Equivalent to `Int8.ofInt`. -/
abbrev Int.toInt8 := Int8.ofInt

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
abbrev Int8.lt (a b : Int8) : Prop :=
  match a.isNeg, b.isNeg with
  | true, true => b.toUInt8 < a.toUInt8
  | true, false => True
  | false, true => False
  | false, false => a.toUInt8 < b.toUInt8
instance : LT Int8 := ⟨Int8.lt⟩

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_lt"]
def Int8.decLt (a b : Int8) : Decidable (Int8.lt a b) := by
  unfold Int8.lt
  match ha : a.isNeg, hb : b.isNeg with
  | true, true => exact inferInstanceAs (Decidable (b.toUInt8 < a.toUInt8))
  | true, false => exact inferInstanceAs (Decidable True)
  | false, true => exact inferInstanceAs (Decidable False)
  | false, false => exact inferInstanceAs (Decidable (a.toUInt8 < b.toUInt8))
instance (a b : Int8) : Decidable (Int8.lt a b) := Int8.decLt a b
instance (a b : Int8) : Decidable (a < b) := Int8.decLt a b

/-- `a` is less than or equal to `b`.-/
def Int8.le (a b : Int8) : Prop :=
  match a.isNeg, b.isNeg with
  | true, true => b.toUInt8 ≤ a.toUInt8
  | true, false => True
  | false, true => False
  | false, false => a.toUInt8 ≤ b.toUInt8
instance : LE Int8 := ⟨Int8.le⟩

-- set_option bootstrap.genMatcherCode false in
-- @[extern "lean_int8_dec_lt"]
def Int8.decLe (a b : Int8) : Decidable (Int8.le a b) := by
  unfold Int8.le
  match ha : a.isNeg, hb : b.isNeg with
  | true, true => exact inferInstanceAs (Decidable (b.toUInt8 ≤ a.toUInt8))
  | true, false => exact inferInstanceAs (Decidable True)
  | false, true => exact inferInstanceAs (Decidable False)
  | false, false => exact inferInstanceAs (Decidable (a.toUInt8 ≤ b.toUInt8))
instance (a b : Int8) : Decidable (Int8.le a b) := Int8.decLe a b
instance (a b : Int8) : Decidable (a ≤ b) := Int8.decLe a b

instance : Max Int8 := maxOfLe
instance : Min Int8 := minOfLe

/-- Returns the log base 2 of `a` for `a ≥ 0`. -/
def Int8.log2 (a : Int8) : Int8 := ⟨UInt8.log2 a.toUInt8⟩

-- @[extern "lean_int8_to_float"] opaque Int8.toFloat (a : Int8) : Float


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
-- Coercions
-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --


-- @[extern "lean_int8_to_int16"]
-- def Int8.toInt16 (a : Int8) : Int16 := a.toInt.toInt16
-- @[extern "lean_int8_to_int32"]
-- def Int8.toInt32 (a : Int8) : Int32 := a.toInt.toInt32
-- @[extern "lean_int8_to_int64"]
-- def Int8.toInt64 (a : Int8) : Int64 := a.toInt.toInt64




-- -- -- -- -- -- -- -- -- -- -- -- -- -- -- -- --
-- Tests

/-- `[to|of]UInt8` tests -/
example : (Int8.ofUInt8 0).toUInt8 = (0 : UInt8) := rfl
example : (Int8.ofUInt8 127).toUInt8 = (127 : UInt8) := rfl
example : (Int8.ofUInt8 128).toUInt8 = (128 : UInt8) := rfl

/-- `Int8.size` test -/
example : Int8.size = (256 : Nat) := rfl

/-- `Int8.maxValue` tests -/
example : Int8.maxValue.toUInt8 = (127 : UInt8) := rfl

/-- `Int8.minValue` tests -/
example : Int8.minValue.toUInt8 = (128 : UInt8) := rfl

/-- `Int8.ofNat` tests -/
example : (Int8.ofNat 0).toUInt8 = (0 : UInt8) := rfl
example : (Int8.ofNat 127).toUInt8 = (127 : UInt8) := rfl
example : (Int8.ofNat 128).toUInt8 = (128 : UInt8) := rfl
example : (Int8.ofNat 255).toUInt8 = (255 : UInt8) := rfl
example : (Int8.ofNat 256).toUInt8 = (256 : UInt8) := rfl

/-- `OfNat` instance for `Int8` tests -/
example : (0 : Int8).toUInt8 = (0 : UInt8) := rfl
example : (127 : Int8).toUInt8 = (127 : UInt8) := rfl
example : (128 : Int8).toUInt8 = (128 : UInt8) := rfl

/-- `Nat.toInt8` tests -/
example : (0 : Nat).toInt8 = (0 : Int8) := rfl
example : (127 : Nat).toInt8 = (127 : Int8) := rfl
example : (128 : Nat).toInt8 = (128 : Int8) := rfl

/-- `Int8.isNeg` tests -/
example : Int8.isNeg 0 = false := rfl
example : Int8.isNeg 127 = false := rfl
example : Int8.isNeg 128 = true := rfl
example : Int8.isNeg 255 = true := rfl
example : Int8.isNeg 256 = false := rfl


/-- `Int8.complement` tests -/
example : (0 : Int8).complement.toUInt8 = (0 : UInt8).complement := rfl
example : (1 : Int8).complement.toUInt8 = (1 : UInt8).complement := rfl
example : (127 : Int8).complement.toUInt8 = (127 : UInt8).complement := rfl
example : (128 : Int8).complement.toUInt8 = (128 : UInt8).complement := rfl

/-- `Compliment` test -/
example : (~~~(1 : Int8)).toUInt8 = (1 : UInt8).complement := rfl

/-- `Int8.neg` tests -/
example : (0 : Int8).neg.toUInt8 = (0 : UInt8) := rfl
example : (1 : Int8).neg.toUInt8 = (255 : UInt8) := rfl
example : (127 : Int8).neg.toUInt8 = (129 : UInt8) := rfl
example : (128 : Int8).neg.toUInt8 = (128 : UInt8) := rfl
example : (255 : Int8).neg.toUInt8 = (1 : UInt8) := rfl

/-- `Int8.toNat` tests -/
example : (0 : Int8).toNat = (0 : Nat) := rfl
example : (127 : Int8).toNat = (127 : Nat) := rfl
/-- `Int8.toNat` of a negative produces 0 a la `Int.toNat`. -/
example : (128 : Int8).toNat = (0 : Nat) := rfl

/-- `Int8.ofInt` tests -/
example : Int8.ofInt (0 : Int) = (0 : Int8) := rfl
example : Int8.ofInt (1 : Int) = (1 : Int8) := rfl
example : Int8.ofInt (2 : Int) = (2 : Int8) := rfl
example : Int8.ofInt (256 : Int) = (0 : Int8) := rfl
example : Int8.ofInt (512 : Int) = (0 : Int8) := rfl
example : Int8.ofInt (127 : Int) = (127 : Int8) := rfl
example : Int8.ofInt (128 : Int) = (128 : Int8) := rfl
example : Int8.ofInt (-1 : Int) = (255 : Int8) := rfl
example : Int8.ofInt (-2 : Int) = (254 : Int8) := rfl
example : Int8.ofInt (-128 : Int) = (128 : Int8) := rfl
example : Int8.ofInt (-129 : Int) = (127 : Int8) := rfl

/-- `Int8.toInt` tests -/
example : (0 : Int8).toInt = (0 : Int) := rfl
example : (1 : Int8).toInt = (1 : Int) := rfl
example : (2 : Int8).toInt = (2 : Int) := rfl
example : (256 : Int8).toInt = (0 : Int) := rfl
example : (512 : Int8).toInt = (0 : Int) := rfl
example : (127 : Int8).toInt = (127 : Int) := rfl
example : (128 : Int8).toInt = (-128 : Int) := rfl
example : (129 : Int8).toInt = (-127 : Int) := rfl
example : (255 : Int8).toInt = (-1 : Int) := rfl
example : (254 : Int8).toInt = (-2 : Int) := rfl

/-- `ToString` tests for `Int8` -/
example : toString (0 : Int8) = "0" := rfl
example : toString (1 : Int8) = "1" := rfl
example : toString (127 : Int8) = "127" := rfl
example : toString (255 : Int8) = "-1" := rfl
example : toString (128 : Int8) = "-128" := rfl

/-- `Int.toInt8` tests -/
example : (0 : Int).toInt8 = (0 : Int8) := rfl
example : (1 : Int).toInt8 = (1 : Int8) := rfl
example : (127 : Int).toInt8 = (127 : Int8) := rfl
example : (128 : Int).toInt8 = (128 : Int8) := rfl
example : (-1 : Int).toInt8 = (255 : Int8) := rfl

/-- `Int8.unsignedAbs` tests -/
example : (0 : Int8).unsignedAbs = (0 : UInt8) := rfl
example : (1 : Int8).unsignedAbs = (1 : UInt8) := rfl
example : (-1 : Int8).unsignedAbs = (1 : UInt8) := rfl
example : (127 : Int8).unsignedAbs = (127 : UInt8) := rfl
example : (-128 : Int8).unsignedAbs = (128 : UInt8) := rfl

/-- `Int8.abs tests -/
example : (0 : Int8).abs = (0 : Int8) := rfl
example : (1 : Int8).abs = (1 : Int8) := rfl
example : (-1 : Int8).abs = (1 : Int8) := rfl
example : (127 : Int8).abs = (127 : Int8) := rfl
example : (-128 : Int8).abs = (-128 : Int8) := rfl

/-- `Int8.add` tests -/
example : Int8.add 0 0 = 0 := rfl
example : Int8.add 0 1 = 1 := rfl
example : Int8.add 1 2 = 3 := rfl
example : Int8.add (-1) 0 = -1 := rfl
example : Int8.add (-1) 1 = 0 := rfl
example : Int8.add 42 42 = 84 := rfl
example : Int8.add 127 0 = 127 := rfl
example : Int8.add 127 (-1) = 127 -1 := rfl
example : Int8.add 127 1 = -128 := rfl
example : Int8.add 127 127 = -2 := rfl
example : Int8.add (-128) 0 = -128 := rfl
example : Int8.add (-128) (-1) = 127 := rfl
example : Int8.add (-128) 1 = -128 + 1 := rfl
example : Int8.add (-128) (-128) = 0 := rfl

/-- `Int8.sub` tests -/
example : Int8.sub 0 0 = 0 := rfl
example : Int8.sub 0 1 = -1 := rfl
example : Int8.sub 1 0 = 1 := rfl
example : Int8.sub 1 2 = -1 := rfl
example : Int8.sub 2 1 = 1 := rfl
example : Int8.sub 2 2 = 0 := rfl
example : Int8.sub (-1) (-1) = 0 := rfl
example : Int8.sub (-1) 1 = (-2) := rfl
example : Int8.sub 127 0 = 127 := rfl
example : Int8.sub 127 1 = 127 - 1 := rfl
example : Int8.sub 127 (-1) = -128 := rfl
example : Int8.sub 127 127 = 0 := rfl
example : Int8.sub (-128) 0 = -128 := rfl
example : Int8.sub (-128) (-1) = -128 + 1 := rfl
example : Int8.sub (-128) 1 = 127 := rfl
example : Int8.sub (-128) (-128) = 0 := rfl

/-- `Int8.mul` tests -/
example : Int8.mul 0  0 = 0 := rfl
example : Int8.mul 0  1 = 0 := rfl
example : Int8.mul 1  2 = 2 := rfl
example : Int8.mul (-1) 0 = 0 := rfl
example : Int8.mul (-1) 1 = (-1) := rfl
example : Int8.mul (-1) 2 = (-2) := rfl
example : Int8.mul 42 2 = 42 * 2 := rfl
example : Int8.mul 127 0 = 0 := rfl
example : Int8.mul 127 1 = 127 := rfl
example : Int8.mul 127 (-1) = -128 + 1 := rfl
example : Int8.mul 127 2 = -2 := rfl
example : Int8.mul (-128) 0 = 0 := rfl
example : Int8.mul (-128) 1 = -128 := rfl
example : Int8.mul (-128) (-1) = -128 := rfl
example : Int8.mul (-128) 2 = 0 := rfl

-- C99, section 6.5.5, paragraph 6:
-- If the quotient a/b is representable,
-- the expression (a/b)*b + a%b shall equal a.
/-- `Int8.div` -/
example : Int8.div 0 1 = 0 := rfl
example : Int8.div 1 0 = 0 := rfl
example : Int8.div 1 1 = 1 := rfl
example : Int8.div (-1) 1 = (-1) := rfl
example : Int8.div 1 (-1) = (-1) := rfl
example : Int8.div 42 1 = 42 := rfl
example : Int8.div 42 2 = 21 := rfl
example : Int8.div 42 3 = 14 := rfl
example : Int8.div 127 1 = 127 := rfl
example : Int8.div 127 (-127) = (-1) := rfl
example : Int8.div (-128) (-1) = (-128) := rfl

-- C99, section 6.5.5, paragraph 6:
-- If the quotient a/b is representable,
-- the expression (a/b)*b + a%b shall equal a.
/-- `Int8.mod` -/
example : Int8.mod 0 1 = 0 := rfl
example : Int8.mod 1 0 = 1 := rfl
example : Int8.mod 1 1 = 0 := rfl
example : Int8.mod 2 1 = 0 := rfl
example : Int8.mod 1 2 = 1 := rfl
example : Int8.mod 42 40 = 2 := rfl
example : Int8.mod (-42) 40 = (-2) := rfl
example : Int8.mod 126 127 = 126 := rfl
example : Int8.mod 126 (-127) = 126 := rfl


/-- `Int8.land` tests -/
example : Int8.land  0 0 =  0 := rfl
example : Int8.land  0 1 =  0 := rfl
example : Int8.land  1 1 =  1 := rfl
example : Int8.land  1 2 =  0 := rfl
example : Int8.land  2 3 =  2 := rfl
example : Int8.land (-128) 127 = 0 := rfl
example : Int8.land 127 (-127) = 1 := rfl

/-- `Int8.lor` -/
example : Int8.lor  0  0 =  0 := rfl
example : Int8.lor  0  1 =  1 := rfl
example : Int8.lor  1  1 =  1 := rfl
example : Int8.lor  1  2 =  3 := rfl
example : Int8.lor  2  3 =  3 := rfl
example : Int8.lor (-128) 127 = (-1) := rfl

/-- `Int8.xor` tests -/
example : Int8.xor  0  0 = 0 := rfl
example : Int8.xor  0  1 = 1 := rfl
example : Int8.xor  1  1 = 0 := rfl
example : Int8.xor  1  2 = 3 := rfl
example : Int8.xor  2  3 = 1 := rfl
example : Int8.xor (-128) 127 = (-1) := rfl
example : Int8.xor 127 (-127) = (-2) := rfl

/-- `Int8.shiftLeft` tests -/
example : Int8.shiftLeft 0  0 = 0 := rfl
example : Int8.shiftLeft 0  1 = 0 := rfl
example : Int8.shiftLeft 1  0 = 1 := rfl
example : Int8.shiftLeft 1  1 = 2 := rfl
example : Int8.shiftLeft (-1) 1 = (-2) := rfl
example : Int8.shiftLeft (-1) 2 = (-4) := rfl
example : Int8.shiftLeft (-128) 1 = 0 := rfl
example : Int8.shiftLeft 127 1 = (-2) := rfl

/-- `Int8.shiftRight` tests -/
example : Int8.shiftRight 1 1 = 0 := rfl
example : Int8.shiftRight 2 1 = 1 := rfl
example : Int8.shiftRight 3 1 = 1 := rfl
example : Int8.shiftRight 4 1 = 2 := rfl
example : Int8.shiftRight 127 6 = 1 := rfl
example : Int8.shiftRight (-1) 1 = 0 := rfl
example : Int8.shiftRight (-2) 1 = (-1) := rfl
example : Int8.shiftRight (-3) 1 = (-1) := rfl
example : Int8.shiftRight (-4) 1 = (-2) := rfl
example : Int8.shiftRight (-127) 6 = (-1) := rfl
example : Int8.shiftRight (-128) 6 = (-2) := rfl

/-- `Int8.lt` tests -/
example : (Int8.lt 1 1) = false := by decide
example : ((1 : Int8) < (1 : Int8)) = false := by decide
example : (Int8.lt 1 2) = true := by decide
example : ((1 : Int8) < (2 : Int8)) = true := by decide
example : (Int8.lt 2 1) = false := by decide
example : ((2 : Int8) < (1 : Int8)) = false := by decide
example : (Int8.lt (-1) 1) = true := by decide
example : ((-1 : Int8) < (1 : Int8)) = true := by decide
example : (Int8.lt 126 127) = true := by decide
example : ((126 : Int8) < (127 : Int8)) = true := by decide
example : (Int8.lt 127 128) = false := by decide
example : ((127 : Int8) < (128 : Int8)) = false := by decide
example : (Int8.lt 128 127) = true := by decide
example : ((128 : Int8) < (127 : Int8)) = true := by decide
example : (Int8.lt 128 128) = false := by decide
example : ((128 : Int8) < (128 : Int8)) = false := by decide
example : (Int8.lt 128 129) = false := by decide
example : ((128 : Int8) < (129 : Int8)) = false := by decide
example : (Int8.lt 129 128) = true := by decide
example : ((129 : Int8) < (128 : Int8)) = true := by decide


/-- `Int8.le` tests -/
example : (Int8.le 1 1) = true := by decide
example : ((1 : Int8) ≤ (1 : Int8)) = true := by decide
example : (Int8.le 1 2) = true := by decide
example : ((1 : Int8) ≤ (2 : Int8)) = true := by decide
example : (Int8.le 2 1) = false := by decide
example : ((2 : Int8) ≤ (1 : Int8)) = false := by decide
example : (Int8.le (-1) 1) = true := by decide
example : ((-1 : Int8) ≤ (1 : Int8)) = true := by decide
example : (Int8.le 126 127) = true := by decide
example : ((126 : Int8) ≤ (127 : Int8)) = true := by decide
example : (Int8.le 127 128) = false := by decide
example : ((127 : Int8) ≤ (128 : Int8)) = false := by decide
example : (Int8.le 128 127) = true := by decide
example : ((128 : Int8) ≤ (127 : Int8)) = true := by decide
example : (Int8.le 128 128) = true := by decide
example : ((128 : Int8) ≤ (128 : Int8)) = true := by decide
example : (Int8.le 128 129) = false := by decide
example : ((128 : Int8) ≤ (129 : Int8)) = false := by decide
example : (Int8.le 129 128) = true := by decide
example : ((129 : Int8) ≤ (128 : Int8)) = true := by decide

/-- `Max Int8` tests -/
example : max (1 : Int8) (2 : Int8) = 2 := rfl
example : max (0 : Int8) (127 : Int8) = 127 := rfl
example : max (0 : Int8) (128 : Int8) = 0 := rfl
example : max (127 : Int8) (128 : Int8) = 127 := rfl
example : max (128 : Int8) (129 : Int8) = 128 := rfl

/-- `Min Int8` tests -/
example : min (1 : Int8) (2 : Int8) = 1 := rfl
example : min (0 : Int8) (127 : Int8) = 0 := rfl
example : min (0 : Int8) (128 : Int8) = 128 := rfl
example : min (127 : Int8) (128 : Int8) = 128 := rfl
example : min (128 : Int8) (129 : Int8) = 129 := rfl
