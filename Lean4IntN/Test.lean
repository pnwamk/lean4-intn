import Lean4IntN.Basic
import Std.Tactic.GuardExpr

structure IntN where
  type : Type u
  size : Nat
  ofInt : Int → type
  toInt : type → Int


abbrev int8Impl : IntN :=
{
  type := Int8,
  size := Int8.size,
  ofInt := Int8.ofInt,
  toInt := Int8.toInt,
}


def IntN.minInt (intN : IntN) : Int := -↑(intN.size >>> 1)
def IntN.maxInt (intN : IntN) : Int := ↑(intN.size >>> 1) - 1

structure UnOpTest (intN : IntN) where
  arg : Int
  opName : String
  op : intN.type → intN.type
  expected : Int

def UnOpTest.run {intN : IntN} (test : UnOpTest intN) : Option String :=
  let actual : Int := intN.toInt <| test.op (intN.ofInt test.arg)
  if actual == test.expected then do
    none
  else
    some s!"{test.opName} {test.arg}) failed: expected {test.expected} but got {actual}"



/-- Check that integers convert to and from IntN as expected for common and edge cases. -/
def intConversionTests (intN : IntN) : List (UnOpTest intN) := [
  (0, 0),
  (1, 1),
  (2, 2),
  (-1, -1),
  (-2, -2),
  (42, 42),
  (-42, -42),
  (intN.minInt, intN.minInt),
  (intN.minInt - 1, intN.maxInt),
  (intN.minInt + 1, intN.minInt + 1),
  (intN.maxInt, intN.maxInt),
  (intN.maxInt - 1, intN.maxInt - 1),
  (intN.maxInt + 1, intN.minInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := intN.ofInt ∘ intN.toInt,
  opName := "intN.ofInt ∘ intN.toInt"
  expected := expected,
}


def negTests (intN : IntN)
  [Neg intN.type]
  : List (UnOpTest intN) := [
  (0, 0),
  (1, -1),
  (-1, 1),
  (intN.minInt, intN.minInt),
  (intN.maxInt, 0 - intN.maxInt),
  (-intN.maxInt, intN.maxInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := Neg.neg,
  opName := "Neg.neg"
  expected := expected
}

def complementTests (intN : IntN)
  [Complement intN.type]
  : List (UnOpTest intN) := [
  (0, -1),
  (-1, 0),
  (1, -2),
  (-2, 1),
  (intN.minInt, intN.maxInt),
  (intN.maxInt, intN.minInt),
].map <| fun (arg, expected) => {
  arg := arg,
  op := Complement.complement,
  opName := "Complement.complement"
  expected := expected
}

structure BinOpTest (intN : IntN) where
  lhs : Int
  rhs : Int
  op : intN.type → intN.type → intN.type
  opName : String
  expected : Int
  isCommutative : Bool := false

def BinOpTest.run {intN : IntN} (test : BinOpTest intN) : Option String :=
  let actual : Int := intN.toInt <| test.op (intN.ofInt test.lhs) (intN.ofInt test.rhs)
  let actual' : Int := intN.toInt <| test.op (intN.ofInt test.rhs) (intN.ofInt test.lhs)
  if actual == test.expected then do
    if test.isCommutative then
      if actual' == test.expected then
        none
      else
        some s!"({test.opName} {test.rhs} {test.lhs}) failed: expected {test.expected} but got {actual'}"
    else
      none
  else
    some s!"({test.opName} {test.lhs} {test.rhs}) failed: expected {test.expected} but got {actual}"


def addTests
  (intN : IntN)
  [Add intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  2,  3),
  (-1,  0,  -1),
  (-1,  1,  0),
  ( 42, 42, 84),
  -- max value addition
  (intN.maxInt, 0,  intN.maxInt),
  (intN.maxInt, -1, intN.maxInt -1),
  (intN.maxInt, 1,  intN.minInt),
  (intN.maxInt, intN.maxInt, -2),
  -- min value addition
  (intN.minInt, 0,           intN.minInt),
  (intN.minInt, -1,          intN.maxInt),
  (intN.minInt, 1,           intN.minInt + 1),
  (intN.minInt, intN.minInt, 0),
].foldr (init := []) <| fun (lhs, rhs, expected) tests => [
  {lhs := lhs,
   rhs := rhs,
   op := Add.add,
   opName := "Add.add",
   expected := expected,
   isCommutative := true,
   : BinOpTest intN},
  ] ++ tests


def subTests
  (intN : IntN)
  [Sub intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  -1),
  ( 1,  0,  1),
  ( 1,  2,  -1),
  ( 2,  1,  1),
  ( 2,  2,  0),
  (-1,  -1,  0),
  (-1,  1,  -2),
  -- max value subtraction
  (intN.maxInt, 0,  intN.maxInt),
  (intN.maxInt, 1, intN.maxInt - 1),
  (intN.maxInt, -1, intN.minInt),
  (intN.maxInt, intN.maxInt, 0),
  -- min value subtraction
  (intN.minInt, 0,           intN.minInt),
  (intN.minInt, -1,          intN.minInt + 1),
  (intN.minInt, 1,           intN.maxInt),
  (intN.minInt, intN.minInt, 0),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Sub.sub,
  opName := "Sub.sub",
  expected := expected,
  : BinOpTest intN
}

def mulTests
  (intN : IntN)
  [Mul intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  2,  2),
  (-1,  0,  0),
  (-1,  1,  -1),
  (-1,  2,  -2),
  ( 42, 2, 42 * 2),
  -- max value addition
  (intN.maxInt, 0,  0),
  (intN.maxInt, 1,  intN.maxInt),
  (intN.maxInt, -1, intN.minInt + 1),
  (intN.maxInt, 2,  -2),
  -- min value addition
  (intN.minInt, 0,  0),
  (intN.minInt, 1,  intN.minInt),
  (intN.minInt, -1, intN.minInt),
  (intN.minInt, 2, 0),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Mul.mul,
  opName := "Mul.mul",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def landTests
  (intN : IntN)
  [AndOp intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  1,  1),
  ( 1,  2,  0),
  ( 2,  3,  2),
  (intN.minInt, intN.maxInt, 0),
  (intN.maxInt, -intN.maxInt, 1),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := AndOp.and,
  opName := "AndOp.and",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def lorTests
  (intN : IntN)
  [OrOp intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  1,  1),
  ( 1,  2,  3),
  ( 2,  3,  3),
  (intN.minInt, intN.maxInt, -1),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := OrOp.or,
  opName := "OrOp.or",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def xorTests
  (intN : IntN)
  [Xor intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  1),
  ( 1,  1,  0),
  ( 1,  2,  3),
  ( 2,  3,  1),
  (intN.minInt, intN.maxInt, -1),
  (intN.maxInt, -intN.maxInt, -2),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := Xor.xor,
  opName := "Xor.xor",
  expected := expected,
  isCommutative := true,
  : BinOpTest intN
}

def shiftLeftTests
  (intN : IntN)
  [ShiftLeft intN.type]
: List (BinOpTest intN) := [
  ( 0,  0,  0),
  ( 0,  1,  0),
  ( 1,  0,  1),
  ( 1,  1,  2),
  ( -1,  1,  -2),
  ( -1,  2,  -4),
  (intN.minInt, 1, 0),
  (intN.maxInt, 1, -2),
].map <| fun (lhs, rhs, expected) => {
  lhs := lhs,
  rhs := rhs,
  op := ShiftLeft.shiftLeft,
  opName := "ShiftLeft.shiftLeft",
  expected := expected,
  : BinOpTest intN
}

-- BOOKMARK
-- Additional sign-sensitive ops:
-- modulo := fun (n m : IntN) : IntN := IntN.ofInt (n.toInt % m.toInt)
-- right shift ...
-- comparisons (except equality) ...


-- FIXME
def divTests
  (intN : IntN)
  [Div intN.type]
: List (BinOpTest intN) := []

-- FIXME
def modTests
  (intN : IntN)
  [Mod intN.type]
: List (BinOpTest intN) := []

-- FIXME
def hmodTests
  (intN : IntN)
  [HMod intN.type Int Int8]
: List (BinOpTest intN) := []

#guard (intConversionTests int8Impl).filterMap UnOpTest.run == []
#guard (negTests int8Impl).filterMap UnOpTest.run == []
#guard (complementTests int8Impl).filterMap UnOpTest.run == []
#guard (addTests int8Impl).filterMap BinOpTest.run == []
#guard (subTests int8Impl).filterMap BinOpTest.run == []
#guard (mulTests int8Impl).filterMap BinOpTest.run == []
#guard (landTests int8Impl).filterMap BinOpTest.run == []
#guard (lorTests int8Impl).filterMap BinOpTest.run == []
#guard (xorTests int8Impl).filterMap BinOpTest.run == []
#guard (shiftLeftTests int8Impl).filterMap BinOpTest.run == []

#eval (-128 : Int8).toUInt8
