import LeanWasm.HList

inductive Size where
  | _32
  | _64
  deriving Inhabited, DecidableEq, Repr

instance : OfNat Size 32 where
  ofNat := ._32

instance : OfNat Size 64 where
  ofNat := ._64

@[simp]
def Size.toNat : Size -> Nat
  | ._32 => 32
  | ._64 => 64

instance : Coe Size Nat where
  coe := Size.toNat

inductive Ty where
  | i : Size -> Ty
  -- | f32 -- Lean doesn't natively support 32-bit floats.
  | f64
  deriving Inhabited, DecidableEq, Repr

@[simp, match_pattern]
abbrev Ty.i32 : Ty := .i 32

@[simp, match_pattern]
abbrev Ty.i64 : Ty := .i 64

instance : ReprAtom Ty where

@[simp]
abbrev Int32 := BitVec 32

@[simp]
abbrev Int64 := BitVec 64

-- https://lean-lang.org/functional_programming_in_lean/dependent-types/universe-pattern.html
@[simp]
abbrev Ty.type (ty : Ty) : Type :=
  match ty with
  | .i s => BitVec s
  | .f64 => Float

-- https://lean-lang.org/theorem_proving_in_lean4/type_classes.html#coercions-using-type-classes
instance : CoeSort Ty Type where
  coe := Ty.type

instance {ty : Ty} : Inhabited ty where
  default :=
    match ty with
    | .i _ => 0
    | .f64 => 0

instance {ty : Ty} : ToString ty where
  toString :=
    match ty with
    | .i _ => toString ∘ BitVec.toInt
    | .f64 => toString

@[simp, match_pattern]
abbrev Stack := HList Ty.type

instance : HAppend (Stack a) (Stack b) (Stack (a ++ b)) where
  hAppend := HList.append

def defaultStack : Stack as :=
  match as with
  | [] => .nil
  | _ :: _ => .cons default defaultStack

def stackToString (s : Stack as) :=
  match s with
  | .nil => "[]."
  | .cons a s => toString a ++ " :. " ++ stackToString s

instance : Inhabited (Stack as) where
  default := defaultStack

instance : ToString (Stack as) where
  toString := stackToString

@[simp, match_pattern]
abbrev Memory := ByteArray
