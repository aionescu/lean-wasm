import LeanWasm.Syntax.Instr

@[pp_using_anonymous_constructor]
structure Context where
  locs : List Ty
  lbls : List (List Ty)
  i : List Ty
  o : List Ty

def Instrs.castPackedContext (es : Instrs knd locs lbls i o) : Instrs knd (Context.mk locs lbls i o).locs (Context.mk locs lbls i o).lbls (Context.mk locs lbls i o).i (Context.mk locs lbls i o).o :=
  es

def Bool.toI32 (b : Bool) : Ty.i32 :=
  BitVec.ofBool b |>.zeroExtend 32

def IBinOp.eval (op : IBinOp) (a b : Ty.i s) : Ty.i s :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

  | .div .s => a.sdiv b
  | .div .u => a.udiv b

  | .rem .s => a.smod b
  | .rem .u => a.umod b

  | .and => a &&& b
  | .or  => a ||| b
  | .xor => a ^^^ b
  | .shl => a <<< b

  | .shr .u => a.sshiftRight b.toNat
  | .shr .s => a.ushiftRight b.toNat

  | .rotl => a.rotateLeft b.toNat
  | .rotr => a.rotateRight b.toNat

def ITestOp.eval (op : ITestOp) (a : Ty.i s) : Ty.i32 :=
  match op with
  | eqz => (a == 0).toI32

def IRelOp.eval (op : IRelOp) (a b : Ty.i s) : Ty.i32 :=
  ( match op with
    | eq => a == b
    | ne => a != b

    | lt .s => a.slt b
    | lt .u => a.ult b

    | gt .s => b.slt a
    | gt .u => b.ult a

    | le .s => a.sle b
    | le .u => a.ule b

    | ge .s => b.sle a
    | ge .u => b.ule a
  ).toI32

def FUnOp.eval : FUnOp -> Ty.f64 -> Ty.f64
  | .neg => .neg
  | .abs => .abs
  | .ceil => .ceil
  | .floor => .floor
  | .sqrt => .sqrt

def FBinOp.eval : FBinOp -> Ty.f64 -> Ty.f64 -> Ty.f64
  | f_add => .add
  | f_sub => .sub
  | f_mul => .mul
  | f_div => .div
  | min => Min.min
  | max => Max.max

def FRelOp.eval (op : FRelOp) (a b : Ty.f64) : Ty.i32 :=
  ( match op with
    | f_eq => a == b
    | f_ne => a != b

    | f_lt => a < b
    | f_gt => a > b
    | f_le => a <= b
    | f_ge => a >= b
  ).toI32

def ByteArray.loadI32LittleEndian (bs : ByteArray) (i : Nat) : Ty.i32 :=
  (bs.get! i).toUInt32
  ||| (bs.get! (i + 1)).toUInt32 <<< 8
  ||| (bs.get! (i + 2)).toUInt32 <<< 16
  ||| (bs.get! (i + 3)).toUInt32 <<< 24
  |>.toNat
  |> BitVec.ofNat 32

def ByteArray.loadI64LittleEndian (bs : ByteArray) (i : Nat) : Ty.i64 :=
  (bs.get! i).toUInt64
  ||| (bs.get! (i + 1)).toUInt64 <<< 8
  ||| (bs.get! (i + 2)).toUInt64 <<< 16
  ||| (bs.get! (i + 3)).toUInt64 <<< 24
  ||| (bs.get! (i + 4)).toUInt64 <<< 32
  ||| (bs.get! (i + 5)).toUInt64 <<< 40
  ||| (bs.get! (i + 6)).toUInt64 <<< 48
  ||| (bs.get! (i + 7)).toUInt64 <<< 56
  |>.toNat
  |> BitVec.ofNat 64

def ByteArray.loadILittleEndian (bs : ByteArray) (i : Ty.i32) : Option (Ty.i s) :=
  if i + (s.toNat / 8) <= bs.size then
    some <| match s with
    | 32 => bs.loadI32LittleEndian i.toNat
    | 64 => bs.loadI64LittleEndian i.toNat
  else
    none

def ByteArray.storeI32LittleEndian (bs : ByteArray) (i : Nat) (n : Ty.i32) : ByteArray :=
  bs
  |>.set! i (UInt8.ofNat (n &&& 0xFF).toNat)
  |>.set! (i + 1) (UInt8.ofNat ((n >>> 8) &&& 0xFF).toNat)
  |>.set! (i + 2) (UInt8.ofNat ((n >>> 16) &&& 0xFF).toNat)
  |>.set! (i + 3) (UInt8.ofNat ((n >>> 24) &&& 0xFF).toNat)

def ByteArray.storeI64LittleEndian (bs : ByteArray) (i : Nat) (n : Ty.i64) : ByteArray :=
  bs
  |>.set! i (UInt8.ofNat (n &&& 0xFF).toNat)
  |>.set! (i + 1) (UInt8.ofNat ((n >>> 8) &&& 0xFF).toNat)
  |>.set! (i + 2) (UInt8.ofNat ((n >>> 16) &&& 0xFF).toNat)
  |>.set! (i + 3) (UInt8.ofNat ((n >>> 24) &&& 0xFF).toNat)
  |>.set! (i + 4) (UInt8.ofNat ((n >>> 32) &&& 0xFF).toNat)
  |>.set! (i + 5) (UInt8.ofNat ((n >>> 40) &&& 0xFF).toNat)
  |>.set! (i + 6) (UInt8.ofNat ((n >>> 48) &&& 0xFF).toNat)
  |>.set! (i + 7) (UInt8.ofNat ((n >>> 56) &&& 0xFF).toNat)

def ByteArray.storeILittleEndian (bs : ByteArray) (i : Ty.i32) (n : Ty.i s) : Option ByteArray :=
  if i + (s.toNat / 8) <= bs.size then
    some <| match s with
    | 32 => bs.storeI32LittleEndian i.toNat n
    | 64 => bs.storeI64LittleEndian i.toNat n
  else
    none

def ByteArray.grow (bs : ByteArray) (a : Ty.i32) : Option ByteArray :=
  let a := a.toNat
  let new_size := bs.size + a

  if bs.size <= new_size then
    some <| bs ++ ⟨Array.mkArray a default⟩
  else
    none
