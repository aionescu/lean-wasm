-- https://lean-lang.org/lean4/doc/examples/deBruijn.lean.html
inductive HList {t : Type v} (f : t -> Type u) : List t -> Type (max u v) where
  | nil : HList f []
  | cons : f a -> HList f as -> HList f (a :: as)

namespace HList.Notation
  @[simp, match_pattern]
  scoped notation:55 a:55 " :. " as:55 => HList.cons a as

  @[simp, match_pattern]
  scoped notation:55 "[]." => HList.nil
end HList.Notation

instance : Inhabited (HList f []) where
  default := .nil

instance [Inhabited (f a)] [Inhabited (HList f as)] : Inhabited (HList f (a :: as)) where
  default := .cons default default

def HList.length (xs : HList f as) : Nat :=
  match xs with
  | .nil => 0
  | .cons _ xs => 1 + xs.length

def HList.head (xs : HList f (a :: as)) : f a :=
  match xs with
  | .cons x _ => x

def HList.tail (xs : HList f (a :: as)) : HList f as :=
  match xs with
  | .cons _ xs => xs

inductive Ix {t : Type u} (a : t) : List t -> Type u where
  | hit : Ix a (a :: as)
  | miss : Ix a as -> Ix a (b :: as)

instance : OfNat (Ix a (a :: as)) 0 where
  ofNat := .hit

instance [o : OfNat (Ix a as) n] : OfNat (Ix a (b :: as)) (n+1) where
  ofNat := .miss o.ofNat

def HList.get (xs : HList f as) (ix : Ix a as) : f a :=
  match ix, xs with
  | .hit, .cons x _ => x
  | .miss ix, .cons _ xs => xs.get ix

def HList.set (xs : HList f as) (ix : Ix a as) (x : f a) : HList f as :=
  match ix, xs with
  | .hit, .cons _ xs => .cons x xs
  | .miss ix, .cons y xs => .cons y (xs.set ix x)

def Ix.ixTy {t : Type u} {a : t} {as : List t} (_ : Ix a as) : t := a

def HList.append (has : HList f as) (hbs : HList f bs) : HList f (as ++ bs) :=
  match has with
  | .nil => hbs
  | .cons a has => .cons a (has.append hbs)

instance : HAppend (HList f a) (HList f b) (HList f (a ++ b)) where
  hAppend := HList.append

def HList.split (as : List t) (l : HList f (as ++ bs)) : HList f as × HList f bs :=
  match as, l with
  | [], l => ⟨.nil, l⟩
  | _ :: as, .cons a l =>
      let ⟨l', l''⟩ := l.split as
      ⟨.cons a l', l''⟩

def HList.take (as : List t) (l : HList f (as ++ bs)) : HList f as := (l.split as).1
def HList.drop (as : List t) (l : HList f (as ++ bs)) : HList f bs := (l.split as).2
