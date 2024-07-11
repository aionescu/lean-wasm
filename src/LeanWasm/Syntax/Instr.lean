import LeanWasm.HList
import LeanWasm.Syntax.Ty

inductive Signedness where
  | s
  | u

inductive IBinOp where
  | add
  | sub
  | mul
  | div : Signedness -> IBinOp
  | rem : Signedness -> IBinOp
  | and
  | or
  | xor
  | shl
  | shr : Signedness -> IBinOp
  | rotl
  | rotr

inductive ITestOp where
  | eqz

inductive IRelOp where
  | eq
  | ne
  | lt : Signedness -> IRelOp
  | gt : Signedness -> IRelOp
  | le : Signedness -> IRelOp
  | ge : Signedness -> IRelOp

inductive FUnOp where
  | neg
  | abs
  | ceil
  | floor
  | sqrt

inductive FBinOp where
  | f_add
  | f_sub
  | f_mul
  | f_div
  | min
  | max

inductive FRelOp where
  | f_eq
  | f_ne
  | f_lt
  | f_gt
  | f_le
  | f_ge

inductive InstrKind where
  | src
  | spec
  | fast

mutual
  inductive Instr : InstrKind -> List Ty -> List (List Ty) -> List Ty -> List Ty -> Type where
    | nop : Instr knd locs lbls i i
    | unreachable : Instr knd locs lbls i o

    | drop : Instr knd locs lbls (t :: i) i
    | const : {t : Ty} -> t -> Instr knd locs lbls i (t :: i) -- Implicitly using CoeSort to coerce `t` to `t.type`

    | i_binop  : IBinOp  -> Instr knd locs lbls (.i s :: .i s :: i) (.i s :: i)
    | i_testop : ITestOp -> Instr knd locs lbls (.i s         :: i) (.i32 :: i)
    | i_relop  : IRelOp  -> Instr knd locs lbls (.i s :: .i s :: i) (.i32 :: i)

    | f_unop  : FUnOp  -> Instr knd locs lbls (.f64         :: i) (.f64 :: i)
    | f_binop : FBinOp -> Instr knd locs lbls (.f64 :: .f64 :: i) (.f64 :: i)
    | f_relop : FRelOp -> Instr knd locs lbls (.f64 :: .f64 :: i) (.i32 :: i)

    | local_get : Ix t locs -> Instr knd locs lbls i (t :: i)
    | local_set : Ix t locs -> Instr knd locs lbls (t :: i) i
    | local_tee : Ix t locs -> Instr knd locs lbls (t :: i) (t :: i)

    | memory_size : Instr knd locs lbls i (.i32 :: i)
    | memory_grow : Instr knd locs lbls (.i32 :: i) (.i32 :: i)

    | i_load : Instr knd locs lbls (.i32 :: i) (.i s :: i)
    | i_store : Instr knd locs lbls (.i s :: .i32 :: i) i

    | block : Instrs knd locs (o :: lbls) i o -> Instr knd locs lbls (i ++ b) (o ++ b)
    | loop  : Instrs knd locs (i :: lbls) i o -> Instr knd locs lbls (i ++ b) (o ++ b)

    | br : Ix i lbls -> Instr knd locs lbls (i ++ b) o
    | br_if : Ix i lbls -> Instr knd locs lbls (.i32 :: i ++ b) (i ++ b)

    -- Administrative instructions
    -- TODO: `k` should be Instrs, not Instr
    | label : (∀ b', Instr .spec locs lbls (i ++ b') (o ++ b')) -> Stack i' -> Instrs .spec locs (i :: lbls) i' o -> Instr .spec locs lbls b (o ++ b)
    | breaking : Ix i' lbls -> Stack (i' ++ b) -> Instr .spec locs lbls i o
    | trapping : Instr .spec locs lbls i o

    | trap : Instr .fast locs lbls i o

  inductive Instrs : InstrKind -> List Ty -> List (List Ty) -> List Ty -> List Ty -> Type where
    | done : Instrs knd locs lbls i i
    | seq : Instr knd locs lbls i o -> Instrs knd locs lbls o o' -> Instrs knd locs lbls i o'
end

namespace Instrs.Notation
  @[simp, match_pattern]
  scoped notation:55 i:55 " ; " is:55 => Instrs.seq i is
end Instrs.Notation

def Instrs.append (as : Instrs knd locs lbls i o) (bs : Instrs knd locs lbls o o') : Instrs knd locs lbls i o' :=
  match as with
  | .done => bs
  | .seq a as => .seq a (as.append bs)

instance : HAppend (Instrs knd locs lbls i o) (Instrs knd locs lbls o o') (Instrs knd locs lbls i o') where
  hAppend := Instrs.append

mutual
  def Instr.toSpec : Instr knd locs lbls i o -> Instr .spec locs lbls i o
    | .nop => .nop
    | .unreachable => .unreachable

    | .drop => .drop
    | .const v => .const v

    | .i_binop op  => .i_binop op
    | .i_testop op => .i_testop op
    | .i_relop op  => .i_relop op

    | .f_unop op  => .f_unop op
    | .f_binop op => .f_binop op
    | .f_relop op => .f_relop op

    | .local_get ix => .local_get ix
    | .local_set ix => .local_set ix
    | .local_tee ix => .local_tee ix

    | .memory_size => .memory_size
    | .memory_grow => .memory_grow

    | .i_load => .i_load
    | .i_store => .i_store

    | .block es => .block es.toSpec
    | .loop es => .loop es.toSpec

    | .br ix => .br ix
    | .br_if ix => .br_if ix

    | .label k vs es => .label k vs es
    | .breaking ix vs => .breaking ix vs
    | .trapping => .trapping

    | .trap => .trapping

  def Instrs.toSpec : Instrs knd locs lbls i o -> Instrs .spec locs lbls i o
    | .done => .done
    | .seq e es => .seq e.toSpec es.toSpec
end

mutual
  def Instr.toFast : Instr .src locs lbls i o -> Instr .fast locs lbls i o
    | .nop => .nop
    | .unreachable => .unreachable

    | .drop => .drop
    | .const v => .const v

    | .i_binop op  => .i_binop op
    | .i_testop op => .i_testop op
    | .i_relop op  => .i_relop op

    | .f_unop op  => .f_unop op
    | .f_binop op => .f_binop op
    | .f_relop op => .f_relop op

    | .local_get ix => .local_get ix
    | .local_set ix => .local_set ix
    | .local_tee ix => .local_tee ix

    | .memory_size => .memory_size
    | .memory_grow => .memory_grow

    | .i_load => .i_load
    | .i_store => .i_store

    | .block es => .block es.toFast
    | .loop es => .loop es.toFast

    | .br ix => .br ix
    | .br_if ix => .br_if ix

  def Instrs.toFast : Instrs .src locs lbls i o -> Instrs .fast locs lbls i o
    | .done => .done
    | .seq e es => .seq e.toFast es.toFast
end

mutual
  -- Explicit weakening function.
  -- Used in a previous version of the interpreter, currently unused.
  def Instr.weaken (b : List Ty) : Instr knd locs lbls i o -> Instr knd locs lbls (i ++ b) (o ++ b)
    | .nop => .nop
    | .unreachable => .unreachable

    | .drop => .drop
    | .const v => .const v

    | .i_binop op  => .i_binop op
    | .i_testop op => .i_testop op
    | .i_relop op  => .i_relop op

    | .f_unop op  => .f_unop op
    | .f_binop op => .f_binop op
    | .f_relop op => .f_relop op

    | .local_get ix => .local_get ix
    | .local_set ix => .local_set ix
    | .local_tee ix => .local_tee ix

    | .memory_size => .memory_size
    | .memory_grow => .memory_grow

    | .i_load => .i_load
    | .i_store => .i_store

    | .block (b := b') (i := i) (o := o) es => List.append_assoc i b' b ▸ List.append_assoc o b' b ▸ .block es
    | .loop (b := b') (i := i) (o := o) es => List.append_assoc i b' b ▸ List.append_assoc o b' b ▸ .loop es

    | .br (b := b') (i := i) (o := o) ix => List.append_assoc i b' b ▸ .br ix
    | .br_if (b := b') (i := i) ix => List.cons_append Ty.i32 (i ++ b') b ▸ List.append_assoc i b' b ▸ .br_if (b := b' ++ b) ix

    | .label (b := b') (o := o) k vs es => List.append_assoc o b' b ▸ .label (b := b' ++ b) k vs es
    | .breaking ix vs => .breaking ix vs
    | .trapping => .trapping

    | .trap => .trap

  def Instrs.weaken (b : List Ty) : Instrs knd locs lbls i o -> Instrs knd locs lbls (i ++ b) (o ++ b)
    | .done => .done
    | .seq e es => .seq (e.weaken b) (es.weaken b)
end
