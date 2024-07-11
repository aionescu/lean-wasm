import LeanWasm.HList
import LeanWasm.Syntax.Instr
import LeanWasm.Eval.Spec

inductive LabelStack (locs : List Ty) : List (List Ty) -> List Ty -> Type where
  | empty : LabelStack locs [] o
  | push : (∀ b', Instr .fast locs lbls (i ++ b') (o ++ b')) -> Stack b -> Instrs .fast locs lbls (o ++ b) o' -> LabelStack locs lbls o' -> LabelStack locs (i :: lbls) o

@[pp_using_anonymous_constructor]
structure FastConfig (c : Context) where
  mem : Memory
  ls : Stack c.locs
  lstk : LabelStack c.locs c.lbls c.o
  vs : Stack c.i
  es : Instrs .fast c.locs c.lbls c.i c.o

inductive FastStep :
  (ctx  : Context) ->
  (ctx' : Context) ->
  FastConfig ctx   ->
  FastConfig ctx'  ->
  Type
where
  | fstep_nop : FastStep ⟨locs, lbls, i, i⟩ ⟨locs, lbls, i, i⟩ ⟨mem, ls, lstk, vs, .seq .nop es⟩ ⟨mem, ls, lstk, vs, es⟩
  | fstep_unreachable : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, vs, .seq .unreachable es⟩ ⟨mem, ls, lstk, vs, .seq .trap es⟩

  | fstep_drop : FastStep ⟨locs, lbls, _ :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq .drop es⟩ ⟨mem, ls, lstk, vs, es⟩
  | fstep_const : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, t :: i, o⟩ ⟨mem, ls, lstk, vs, .seq (.const a) es⟩ ⟨mem, ls, lstk, .cons a vs, es⟩

  | fstep_i_binop : FastStep ⟨locs, lbls, .i s :: .i s :: i, o⟩ ⟨locs, lbls, .i s :: i, o⟩ ⟨mem, ls, lstk, .cons b (.cons a vs), .seq (.i_binop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a b) vs, es⟩
  | fstep_i_testop : FastStep ⟨locs, lbls, .i s :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq (.i_testop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a) vs, es⟩
  | fstep_i_relop : FastStep ⟨locs, lbls, .i s :: .i s :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, lstk, .cons b (.cons a vs), .seq (.i_relop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a b) vs, es⟩

  | fstep_f_unop : FastStep ⟨locs, lbls, .f64 :: i, o⟩ ⟨locs, lbls, .f64 :: i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq (.f_unop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a) vs, es⟩
  | fstep_f_binop : FastStep ⟨locs, lbls, .f64 :: .f64 :: i, o⟩ ⟨locs, lbls, .f64 :: i, o⟩ ⟨mem, ls, lstk, .cons b (.cons a vs), .seq (.f_binop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a b) vs, es⟩
  | fstep_f_relop : FastStep ⟨locs, lbls, .f64 :: .f64 :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, lstk, .cons b (.cons a vs), .seq (.f_relop op) es⟩ ⟨mem, ls, lstk, .cons (op.eval a b) vs, es⟩

  | fstep_local_get : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, _ :: i, o⟩ ⟨mem, ls, lstk, vs, .seq (.local_get ix) es⟩ ⟨mem, ls, lstk, .cons (ls.get ix) vs, es⟩
  | fstep_local_set : FastStep ⟨locs, lbls, _ :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq (.local_set ix) es⟩ ⟨mem, ls.set ix a, lstk, vs, es⟩
  | fstep_local_tee : FastStep ⟨locs, lbls, t :: i, o⟩ ⟨locs, lbls, t :: i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq (.local_tee ix) es⟩ ⟨mem, ls.set ix a, lstk, .cons a vs, es⟩

  | fstep_memory_size : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, lstk, vs, .seq .memory_size es⟩ ⟨mem, ls, lstk, .cons mem.size vs, es⟩

  | fstep_memory_grow_trap : mem.grow a = none -> FastStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq .memory_grow es⟩ ⟨mem, ls, lstk, vs, .seq .trap es⟩
  | fstep_memory_grow_ok : mem.grow a = some mem' -> FastStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, lstk, .cons a vs, .seq .memory_grow es⟩ ⟨mem', ls, lstk, .cons mem'.size vs, es⟩

  | fstep_i_load_trap : mem.loadILittleEndian addr = none -> FastStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons addr vs, .seq .i_load es⟩ ⟨mem, ls, lstk, vs, .seq .trap es⟩
  | fstep_i_load_ok : mem.loadILittleEndian addr = some (α := Ty.i s) a -> FastStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, .i s :: i, o⟩ ⟨mem, ls, lstk, .cons addr vs, .seq .i_load es⟩ ⟨mem, ls, lstk, .cons a vs, es⟩

  | fstep_i_store_trap : mem.storeILittleEndian addr a = none -> FastStep ⟨locs, lbls, .i s :: .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons a (.cons addr vs), .seq .i_store es⟩ ⟨mem, ls, lstk, vs, .seq .trap es⟩
  | fstep_i_store_ok : mem.storeILittleEndian addr a = some mem' -> FastStep ⟨locs, lbls, .i s :: .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, .cons a (.cons addr vs), .seq .i_store es⟩ ⟨mem', ls, lstk, vs, es⟩

  | fstep_block : FastStep ⟨locs, lbls, i' ++ i, o⟩ ⟨locs, o  :: lbls, i', o⟩ ⟨mem, ls, lstk, vs' ++ vs, .seq (.block es') es⟩ ⟨mem, ls, .push (λ _ => .nop)      vs es lstk, vs', es'⟩
  | fstep_loop  : FastStep ⟨locs, lbls, i' ++ i, o⟩ ⟨locs, i' :: lbls, i', o⟩ ⟨mem, ls, lstk, vs' ++ vs, .seq (.loop  es') es⟩ ⟨mem, ls, .push (λ _ => .loop es') vs es lstk, vs', es'⟩

  | fstep_br_hit  : FastStep ⟨locs, l :: lbls, l ++ i, o⟩ ⟨locs, lbls, l ++ i', o⟩ ⟨mem, ls, .push k vs' es' lstk, vs, .seq (.br .hit)       es⟩ ⟨mem, ls, lstk, vs.take _ ++ vs', .seq (k _) es'⟩
  | fstep_br_miss : FastStep ⟨locs, l :: lbls, l ++ i, o⟩ ⟨locs, lbls, l ++ i,  o⟩ ⟨mem, ls, .push k vs' es' lstk, vs, .seq (.br (.miss ix)) es⟩ ⟨mem, ls, lstk, vs,               .seq (.br ix) es'⟩

  | fstep_br_if_false : FastStep ⟨locs, lbls, .i32 :: i ++ i', o⟩ ⟨locs, lbls, i ++ i', o⟩ ⟨mem, ls, lstk, List.cons_append _ _ _ ▸ .cons 0 vs, .seq (.br_if ix) es⟩ ⟨mem, ls, lstk, vs, es⟩
  | fstep_br_if_true  : FastStep ⟨locs, lbls, .i32 :: i ++ i', o⟩ ⟨locs, lbls, i ++ i', o⟩ ⟨mem, ls, lstk, List.cons_append _ _ _ ▸ .cons n vs, .seq (.br_if ix) es⟩ ⟨mem, ls, lstk, vs, .seq (.br ix) es⟩

  | fstep_done_empty : FastStep ⟨locs, [], i, i⟩ ⟨locs, [], i, i⟩ ⟨mem, ls, .empty, vs, .done⟩ ⟨mem, ls, .empty, vs, .done⟩
  | fstep_done_push  : FastStep ⟨locs, l :: lbls, i, i⟩ ⟨locs, lbls, i ++ i', o⟩ ⟨mem, ls, .push k vs' es lstk, vs, .done⟩ ⟨mem, ls, lstk, vs ++ vs', es⟩

  | fstep_trap : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, vs, .seq .trap es⟩ ⟨mem, ls, lstk, vs, .seq .trap .done⟩

inductive FastSteps :
  (ctx  : Context) ->
  (ctx' : Context) ->
  FastConfig ctx   ->
  FastConfig ctx'  ->
  Type
where
  | fsteps_refl : FastSteps ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, lstk, vs, es⟩ ⟨mem, ls, lstk, vs, es⟩
  | fsteps_trans :
      FastStep  ⟨locs, lbls,  i,  o ⟩ ⟨locs, lbls',  i',  o' ⟩ ⟨mem,  ls,  lstk,  vs,  es ⟩ ⟨mem',  ls',  lstk',  vs',  es' ⟩ ->
      FastSteps ⟨locs, lbls', i', o'⟩ ⟨locs, lbls'', i'', o''⟩ ⟨mem', ls', lstk', vs', es'⟩ ⟨mem'', ls'', lstk'', vs'', es''⟩ ->
      FastSteps ⟨locs, lbls,  i,  o ⟩ ⟨locs, lbls'', i'', o''⟩ ⟨mem,  ls,  lstk,  vs,  es ⟩ ⟨mem'', ls'', lstk'', vs'', es''⟩

def FastConfig.isFinal_unpacked
  (_mem : Memory) (_ls : Stack locs) (lstk : LabelStack locs lbls o) (_vs : Stack i) (es : Instrs .fast locs lbls i o)
  : Bool
:=
  match lstk, es with
  | .empty, .done => true
  | _, .seq .trap _ => true
  | _, _ => false

def FastConfig.isFinal (cfg : FastConfig ctx) : Bool :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ => FastConfig.isFinal_unpacked mem ls lstk vs es

def FastConfig.isTrap_unpacked
  (_mem : Memory) (_ls : Stack locs) (_lstk : LabelStack locs lbls o) (_vs : Stack i) (es : Instrs .fast locs lbls i o)
  : Bool
:=
  match es with
  | .seq .trap _ => true
  | _ => false

def FastConfig.isTrap (cfg : FastConfig ctx) : Bool :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ => FastConfig.isTrap_unpacked mem ls lstk vs es


def FastConfig.eval_unpacked
  (mem : Memory) (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .fast locs lbls i o)
  : Σ lbls', Σ i', Σ o', Memory × Stack locs × LabelStack locs lbls' o' × Stack i' × Instrs .fast locs lbls' i' o'
:=
  match es with
  | .done =>
      match lstk with
      | .empty => ⟨_, _, _, mem, ls, .empty, vs, .done⟩
      | .push _ vs' es lstk => ⟨_, _, _, mem, ls, lstk, vs ++ vs', es⟩
  | .seq e es =>
      match e, vs with
      | .nop, vs => ⟨_, _, _, mem, ls, lstk, vs, es⟩
      | .unreachable, vs => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es⟩

      | .drop, .cons _ vs => ⟨_, _, _, mem, ls, lstk, vs, es⟩
      | .const a, vs => ⟨_, _, _, mem, ls, lstk, .cons a vs, es⟩

      | .i_binop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es⟩
      | .i_testop op, .cons a vs => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a) vs, es⟩
      | .i_relop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es⟩

      | .f_unop op, .cons a vs => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a) vs, es⟩
      | .f_binop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es⟩
      | .f_relop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es⟩

      | .local_get ix, vs => ⟨_, _, _, mem, ls, lstk, .cons (ls.get ix) vs, es⟩
      | .local_set ix, .cons a vs => ⟨_, _, _, mem, ls.set ix a, lstk, vs, es⟩
      | .local_tee ix, .cons a vs => ⟨_, _, _, mem, ls.set ix a, lstk, .cons a vs, es⟩

      | .memory_size, vs => ⟨_, _, _, mem, ls, lstk, .cons mem.size vs, es⟩
      | .memory_grow, .cons a vs =>
          match mem.grow a with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es⟩
          | some mem' => ⟨_, _, _, mem', ls, lstk, .cons mem'.size vs, es⟩

      | .i_load, .cons addr vs =>
          match mem.loadILittleEndian addr with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es⟩
          | some a => ⟨_, _, _, mem, ls, lstk, .cons a vs, es⟩

      | .i_store, .cons a (.cons addr vs) =>
          match mem.storeILittleEndian addr a with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es⟩
          | some mem' => ⟨_, _, _, mem', ls, lstk, vs, es⟩

      | .block es', vs => ⟨_, _, _, mem, ls, .push (λ _ => .nop)      (vs.drop _) es lstk, (vs.take _), es'⟩
      | .loop es',  vs => ⟨_, _, _, mem, ls, .push (λ _ => .loop es') (vs.drop _) es lstk, (vs.take _), es'⟩

      | .br ix, vs =>
          match lstk, ix with
          | .push k vs' es' lstk, .hit => ⟨_, _, _, mem, ls, lstk, vs.take _ ++ vs', .seq (k _) es'⟩
          | .push _k _vs' es' lstk, .miss ix => ⟨_, _, _, mem, ls, lstk, vs, .seq (.br ix) es'⟩

      | .br_if ix, .cons v vs =>
          match v with
          | 0 => ⟨_, _, _, mem, ls, lstk, vs, es⟩
          | _ => ⟨_, _, _, mem, ls, lstk, vs, .seq (.br ix) es⟩

      | .trap, vs => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap .done⟩

def FastConfig.evals_unpacked
  (mem : Memory) (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .fast locs lbls i o)
  (fuel : Nat)
  : Σ lbls', Σ i', Σ o', Memory × Stack locs × LabelStack locs lbls' o' × Stack i' × Instrs .fast locs lbls' i' o'
:=
  match fuel with
  | 0 => ⟨_, _, _, mem, ls, lstk, vs, es⟩
  | fuel + 1 =>
      if FastConfig.isFinal_unpacked mem ls lstk vs es then
        ⟨_, _, _, mem, ls, lstk, vs, es⟩
      else
        let ⟨_, _, _, mem', ls', lstk', vs', es'⟩ := FastConfig.eval_unpacked mem ls lstk vs es
        FastConfig.evals_unpacked mem' ls' lstk' vs' es' fuel

def FastConfig.eval (cfg : FastConfig ctx) : Σ ctx', FastConfig ctx' :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ =>
      match FastConfig.eval_unpacked mem ls lstk vs es with
      | ⟨lbls', i', o', mem', ls', lstk', vs', es'⟩ => ⟨⟨ctx.locs, lbls', i', o'⟩, ⟨mem', ls', lstk', vs', es'⟩⟩

def FastConfig.evals (cfg : FastConfig ctx) (fuel : Nat) : Σ ctx', FastConfig ctx' :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ =>
      match FastConfig.evals_unpacked mem ls lstk vs es fuel with
      | ⟨lbls', i', o', mem', ls', lstk', vs', es'⟩ => ⟨⟨ctx.locs, lbls', i', o'⟩, ⟨mem', ls', lstk', vs', es'⟩⟩

def FastConfig.eval_unpacked_proofCarrying
  {locs : List Ty} {lbls : List (List Ty)} {i o : List Ty}
  (mem : Memory) (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .fast locs lbls i o)
  : Σ lbls', Σ i', Σ o', (mem' : Memory) × (ls' : Stack locs) × (lstk' : LabelStack locs lbls' o') × (vs' : Stack i') × (es' : Instrs .fast locs lbls' i' o') × FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls', i', o'⟩ ⟨mem, ls, lstk, vs, es⟩ ⟨mem', ls', lstk', vs', es'⟩
:=
  match locs, lbls, i, o, es with
  | _, _, _, _, .done =>
      match lstk with
      | .empty => ⟨_, _, _, mem, ls, .empty, vs, .done, .fstep_done_empty⟩
      | .push _ vs' es lstk => ⟨_, _, _, mem, ls, lstk, vs ++ vs', es, .fstep_done_push⟩
  | locs, lbls, i, o, .seq (i := .(i)) (o := o') (o' := .(o)) e es =>
      match i, o', o, e, vs with
      | i, _, _, .nop (i := .(i)), vs => ⟨_, _, _, mem, ls, lstk, vs, es, sorry⟩ -- .fstep_nop⟩
      | _, _, _, .unreachable, vs => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es, .fstep_unreachable⟩

      | _, _, _, .drop, .cons _ vs => ⟨_, _, _, mem, ls, lstk, vs, es, .fstep_drop⟩
      | _, _, _, .const a, vs => ⟨_, _, _, mem, ls, lstk, .cons a vs, es, .fstep_const⟩

      | _, _, _, .i_binop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es, .fstep_i_binop⟩
      | _, _, _, .i_testop op, .cons a vs => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a) vs, es, .fstep_i_testop⟩
      | _, _, _, .i_relop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es, .fstep_i_relop⟩

      | _, _, _, .f_unop op, .cons a vs => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a) vs, es, .fstep_f_unop⟩
      | _, _, _, .f_binop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es, .fstep_f_binop⟩
      | _, _, _, .f_relop op, .cons b (.cons a vs) => ⟨_, _, _, mem, ls, lstk, .cons (op.eval a b) vs, es, .fstep_f_relop⟩

      | _, _, _, .local_get ix, vs => ⟨_, _, _, mem, ls, lstk, .cons (ls.get ix) vs, es, .fstep_local_get⟩
      | _, _, _, .local_set ix, .cons a vs => ⟨_, _, _, mem, ls.set ix a, lstk, vs, es, .fstep_local_set⟩
      | _, _, _, .local_tee ix, .cons a vs => ⟨_, _, _, mem, ls.set ix a, lstk, .cons a vs, es, .fstep_local_tee⟩

      | _, _, _, .memory_size, vs => ⟨_, _, _, mem, ls, lstk, .cons mem.size vs, es, .fstep_memory_size⟩
      | _, _, _, .memory_grow, .cons a vs =>
          match h : mem.grow a with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es, .fstep_memory_grow_trap h⟩
          | some mem' => ⟨_, _, _, mem', ls, lstk, .cons mem'.size vs, es, .fstep_memory_grow_ok h⟩

      | _, _, _, .i_load, .cons addr vs =>
          match h : mem.loadILittleEndian addr with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es, .fstep_i_load_trap h⟩
          | some a => ⟨_, _, _, mem, ls, lstk, .cons a vs, es, .fstep_i_load_ok h⟩

      | _, _, _, .i_store, .cons a (.cons addr vs) =>
          match h : mem.storeILittleEndian addr a with
          | none => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap es, .fstep_i_store_trap h⟩
          | some mem' => ⟨_, _, _, mem', ls, lstk, vs, es, .fstep_i_store_ok h⟩

      | _, _, _, .block es', vs => ⟨_, _, _, mem, ls, .push (λ _ => .nop)      (vs.drop _) es lstk, (vs.take _), es', sorry⟩ -- .fstep_block⟩
      | _, _, _, .loop es',  vs => ⟨_, _, _, mem, ls, .push (λ _ => .loop es') (vs.drop _) es lstk, (vs.take _), es', sorry⟩ -- .fstep_loop⟩

      | _, _, _, .br ix, vs =>
          match lbls, lstk, ix with
          | _, .push k vs' es' lstk, .hit => ⟨_, _, _, mem, ls, lstk, vs.take _ ++ vs', .seq (k _) es', sorry⟩ -- .fstep_br_hit⟩
          | _, .push _k _vs' es' lstk, .miss ix => ⟨_, _, _, mem, ls, lstk, vs, .seq (.br ix) es', sorry⟩ -- .fstep_br_miss⟩

      | _, _, _, .br_if ix, .cons v vs =>
          match v with
          | 0 => ⟨_, _, _, mem, ls, lstk, vs, es, .fstep_br_if_false⟩
          | _ => ⟨_, _, _, mem, ls, lstk, vs, .seq (.br ix) es, .fstep_br_if_true⟩

      | _, _, _, .trap, vs => ⟨_, _, _, mem, ls, lstk, vs, .seq .trap .done, .fstep_trap⟩

def FastConfig.evals_unpacked_proofCarrying
  {locs : List Ty} {lbls : List (List Ty)} {i o : List Ty}
  (mem : Memory) (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .fast locs lbls i o)
  (fuel : Nat)
  : Σ lbls', Σ i', Σ o', (mem' : Memory) × (ls' : Stack locs) × (lstk' : LabelStack locs lbls' o') × (vs' : Stack i') × (es' : Instrs .fast locs lbls' i' o') × FastSteps ⟨locs, lbls, i, o⟩ ⟨locs, lbls', i', o'⟩ ⟨mem, ls, lstk, vs, es⟩ ⟨mem', ls', lstk', vs', es'⟩
:=
  match fuel with
  | 0 => ⟨_, _, _, mem, ls, lstk, vs, es, .fsteps_refl⟩
  | fuel + 1 =>
      if FastConfig.isFinal_unpacked mem ls lstk vs es then
        ⟨_, _, _, mem, ls, lstk, vs, es, .fsteps_refl⟩
      else
        let ⟨_, _, _, mem', ls', lstk', vs', es', fstep⟩ := FastConfig.eval_unpacked_proofCarrying mem ls lstk vs es
        let ⟨_, _, _, mem'', ls'', lstk'', vs'', es'', fsteps⟩ := FastConfig.evals_unpacked_proofCarrying mem' ls' lstk' vs' es' fuel
        ⟨_, _, _, mem'', ls'', lstk'', vs'', es'', .fsteps_trans fstep fsteps⟩

def FastConfig.eval_proofCarrying (cfg : FastConfig ctx) : Σ ctx', (cfg' : FastConfig ctx') × FastStep ctx ctx' cfg cfg' :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ =>
      match FastConfig.eval_unpacked_proofCarrying mem ls lstk vs es with
      | ⟨lbls', i', o', mem', ls', lstk', vs', es', fstep⟩ => ⟨⟨ctx.locs, lbls', i', o'⟩, ⟨mem', ls', lstk', vs', es'⟩, fstep⟩

def FastConfig.evals_proofCarrying (cfg : FastConfig ctx) (fuel : Nat) : Σ ctx', (cfg' : FastConfig ctx') × FastSteps ctx ctx' cfg cfg' :=
  match cfg with
  | ⟨mem, ls, lstk, vs, es⟩ =>
      match FastConfig.evals_unpacked_proofCarrying mem ls lstk vs es fuel with
      | ⟨lbls', i', o', mem', ls', lstk', vs', es', fsteps⟩ => ⟨⟨ctx.locs, lbls', i', o'⟩, ⟨mem', ls', lstk', vs', es'⟩, fsteps⟩

def FastConfig.toSpecContext_unpacked
  (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  : Context
:=
  match lstk with
  | .empty => ⟨locs, lbls, i, o⟩
  | .push k vs' es' lstk => FastConfig.toSpecContext_unpacked lstk vs' (.seq (.label (λ b => (k b).toSpec) vs es.toSpec) es'.toSpec)

def FastConfig.toSpecContext : FastConfig ctx -> Context
  | ⟨_, _, lstk, vs, es⟩ => FastConfig.toSpecContext_unpacked lstk vs es.toSpec

def FastConfig.toSpec_unpacked
  (mem : Memory) (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  : SpecConfig (FastConfig.toSpecContext_unpacked lstk vs es)
:=
  match lbls, lstk with
  | _, .empty => ⟨mem, ls, vs, es⟩
  | _ :: _, .push k vs' es' lstk => FastConfig.toSpec_unpacked mem ls lstk vs' (.seq (.label (λ b => (k b).toSpec) vs es.toSpec) es'.toSpec)

def FastConfig.toSpec : (cfg : FastConfig ctx) -> SpecConfig cfg.toSpecContext
  | ⟨mem, ls, lstk, vs, es⟩ => FastConfig.toSpec_unpacked mem ls lstk vs es.toSpec

---------------------------------------- Old proof attempts ----------------------------------------

-- def fast_eval_sound
--   {locs : List Ty} {lbls : List (List Ty)} {i o : List Ty}
--   (ls : Stack locs) (lstk : LabelStack locs lbls o) (vs : Stack i) (es : Instrs .fast locs lbls i o)
--   {lbls' : List (List Ty)} {i' o' : List Ty}
--   (ls' : Stack locs) (lstk' : LabelStack locs lbls' o') (vs' : Stack i') (es' : Instrs .fast locs lbls' i' o')
--   (h : @fast_eval_unpacked locs lbls i o ls lstk vs es = ⟨lbls', i', o', ls', lstk', vs', es'⟩)
--   : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls', i', o'⟩ ⟨ls, lstk, vs, es⟩ ⟨ls', lstk', vs', es'⟩
-- :=
--   match o, es with
--   | .(i), .done =>
--       match lstk with
--       | .empty => h ▸ .fstep_done_empty
--       | .push _ vs' es lstk => ⟨_, _, _, ls, lstk, vs ++ vs', es⟩
--   | _, .seq e es =>
--       match e, vs with
--       | .nop, vs => ⟨_, _, _, ls, lstk, vs, es⟩
--       | .drop, .cons _ vs => ⟨_, _, _, ls, lstk, vs, es⟩

--       | .const a, vs => ⟨_, _, _, ls, lstk, .cons a vs, es⟩

--       | .i_binop op, .cons b (.cons a vs) => ⟨_, _, _, ls, lstk, .cons (op.eval a b) vs, es⟩
--       | .i_testop op, .cons a vs => ⟨_, _, _, ls, lstk, .cons (op.eval a) vs, es⟩
--       | .i_relop op, .cons b (.cons a vs) => ⟨_, _, _, ls, lstk, .cons (op.eval a b) vs, es⟩

--       | .f_unop op, .cons a vs => ⟨_, _, _, ls, lstk, .cons (op.eval a) vs, es⟩
--       | .f_binop op, .cons b (.cons a vs) => ⟨_, _, _, ls, lstk, .cons (op.eval a b) vs, es⟩
--       | .f_relop op, .cons b (.cons a vs) => ⟨_, _, _, ls, lstk, .cons (op.eval a b) vs, es⟩

--       | .local_get ix, vs => ⟨_, _, _, ls, lstk, .cons (ls.get ix) vs, es⟩
--       | .local_set ix, .cons a vs => ⟨_, _, _, ls.set ix a, lstk, vs, es⟩
--       | .local_tee ix, .cons a vs => ⟨_, _, _, ls.set ix a, lstk, .cons a vs, es⟩

--       | .block es', vs => ⟨_, _, _, ls, .push (λ _ => .nop)      (vs.drop _) es lstk, (vs.take _), es'⟩
--       | .loop es',  vs => ⟨_, _, _, ls, .push (λ _ => .loop es') (vs.drop _) es lstk, (vs.take _), es'⟩

--       | .br .hit, vs =>
--           match lstk with
--           | .push k vs' es' lstk => ⟨_, _, _, ls, lstk, vs.take _ ++ vs', .seq (k _) es'⟩
--       | .br (.miss ix), vs =>
--           match lstk with
--           | .push _k _vs' es' lstk => ⟨_, _, _, ls, lstk, vs, .seq (.br ix) es'⟩

--       | .br_if ix, .cons v vs =>
--           match v with
--           | 0 => ⟨_, _, _, ls, lstk, vs, es⟩
--           | _ => ⟨_, _, _, ls, lstk, vs, .seq (.br ix) es⟩

-- def fast_eval_correct
--   (fstep : FastStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls', i', o'⟩ ⟨ls, lstk, vs, es⟩ ⟨ls', lstk', vs', es'⟩)
--   : fast_eval_unpacked ls lstk vs es = ⟨lbls', i', o', ls', lstk', vs', es'⟩
-- := by
--   match fstep with
--   | .fstep_nop => simp [fast_eval_unpacked]
--   | .fstep_drop => simp [fast_eval_unpacked]

--   | .fstep_const => simp [fast_eval_unpacked]

--   | .fstep_i_binop => simp [fast_eval_unpacked]
--   | .fstep_i_testop => simp [fast_eval_unpacked]
--   | .fstep_i_relop => simp [fast_eval_unpacked]

--   | .fstep_f_unop => simp [fast_eval_unpacked]
--   | .fstep_f_binop => simp [fast_eval_unpacked]
--   | .fstep_f_relop => simp [fast_eval_unpacked]

--   | .fstep_local_get => simp [fast_eval_unpacked]
--   | .fstep_local_set => simp [fast_eval_unpacked]
--   | .fstep_local_tee => simp [fast_eval_unpacked]

--   | .fstep_block => simp [fast_eval_unpacked]
--   | .fstep_loop => simp [fast_eval_unpacked]

--   | .fstep_br_hit => simp [fast_eval_unpacked]
--   | .fstep_br_miss => simp [fast_eval_unpacked]

--   | .fstep_br_if_false => simp [fast_eval_unpacked]
--   | .fstep_br_if_true => simp [fast_eval_unpacked]

--   | .fstep_done_empty => simp [fast_eval_unpacked]
--   | .fstep_done_push => simp [fast_eval_unpacked]

-- theorem correct :
--   {locs : List Ty} ->
--   {lbls  : List (List Ty)} -> {i  o  : List Ty} ->
--   {lbls' : List (List Ty)} -> {i' o' : List Ty} ->
--   {vs  : Stack locs} -> {fs  : Frames locs lbls  o } -> {is  : Stack i } -> {es  : Instrs locs lbls  i  o } ->
--   {vs' : Stack locs} -> {fs' : Frames locs lbls' o'} -> {is' : Stack i'} -> {es' : Instrs locs lbls' i' o'} ->
--   Step ⟨vs, fs, is, es⟩ ⟨vs', fs', is', es'⟩ ->
--   eval vs fs is es = ⟨lbls', i', o', vs', fs', is', es'⟩
-- := λ step => sorry
--   -- match step with
--   -- | .step_end_empty => by simp [eval]
--   -- | .step_end_push => by simp [eval]

--   -- | .step_drop => by simp [eval]
--   -- | .step_dup => by simp [eval]

--   -- | .step_i32_const => by simp [eval]
--   -- | .step_i32_add => by simp [eval]

--   -- | .step_local_get => by simp [eval]
--   -- | .step_local_set => by simp [eval]

--   -- | .step_block => by simp [eval]
--   -- | .step_loop => by simp [eval]
--   -- | .step_br => by simp [eval]

-- theorem corrects_lemma :
--   {locs : List Ty} ->
--   {lbls   : List (List Ty)} -> {i   o   : List Ty} ->
--   {lbls'  : List (List Ty)} -> {i'  o'  : List Ty} ->
--   {lbls'' : List (List Ty)} -> {i'' o'' : List Ty} ->
--   {vs   : Stack locs} -> {fs   : Frames locs lbls   o  } -> {is   : Stack i  } -> {es   : Instrs locs lbls   i   o  } ->
--   {vs'  : Stack locs} -> {fs'  : Frames locs lbls'  o' } -> {is'  : Stack i' } -> {es'  : Instrs locs lbls'  i'  o' } ->
--   {vs'' : Stack locs} -> {fs'' : Frames locs lbls'' o''} -> {is'' : Stack i''} -> {es'' : Instrs locs lbls'' i'' o''} ->
--   {fuel : Nat} ->
--   eval vs fs is es = ⟨lbls', i', o', vs', fs', is', es'⟩ ->
--   evals vs' fs' is' es' fuel = ⟨lbls'', i'', o'', vs'', fs'', is'', es''⟩ ->
--   evals vs fs is es (fuel + 1) = ⟨lbls'', i'', o'', vs'', fs'', is'', es''⟩
-- := λ eq eqs => sorry

-- theorem corrects :
--   {locs : List Ty} ->
--   {lbls  : List (List Ty)} -> {i  o  : List Ty} ->
--   {lbls' : List (List Ty)} -> {i' o' : List Ty} ->
--   {vs  : Stack locs} -> {fs  : Frames locs lbls  o } -> {is  : Stack i } -> {es  : Instrs locs lbls  i  o } ->
--   {vs' : Stack locs} -> {fs' : Frames locs lbls' o'} -> {is' : Stack i'} -> {es' : Instrs locs lbls' i' o'} ->
--   Steps ⟨vs, fs, is, es⟩ ⟨vs', fs', is', es'⟩ ->
--   Σ' fuel, evals vs fs is es fuel = ⟨lbls', i', o', vs', fs', is', es'⟩
-- := λ steps =>
--   match steps with
--   | .steps_refl => ⟨0, rfl⟩
--   | .steps_trans step steps =>
--       let ⟨fuel, proof⟩ := corrects steps
--       ⟨fuel + 1, corrects_lemma (correct step) proof⟩

-- def fstep_ssteps
--   (fcfg  : FastConfig fctx )
--   (fcfg' : FastConfig fctx')
--   (fstep : FastStep fctx fctx' fcfg fcfg')

--   (sctx  : SpecCtx)
--   (sctx' : SpecCtx)
--   (scfg  : SConfig sctx )
--   (scfg' : SConfig sctx')

--   (hargs  : sctx  = fcfg.toSpecCtx )
--   (hargs' : sctx' = fcfg'.toSpecCtx)
--   (hcfg  : scfg  = hargs  ▸ fcfg.toSpec )
--   (hcfg' : scfg' = hargs' ▸ fcfg'.toSpec)

--   : SStep sctx sctx' scfg scfg'
-- :=
--   match fstep with
--   | .fstep_nop => .sstep_nop
--   | _ => sorry

-- def fstep_ssteps
--   (fcfg  : FastConfig fctx )
--   (fcfg' : FastConfig fctx')
--   (fstep : FastStep fctx fctx' fcfg fcfg')

--   : SStep fcfg.toSpecCtx fcfg'.toSpecCtx fcfg.toSpec fcfg'.toSpec
-- :=
--   match fctx, fctx', fcfg, fcfg', fcfg.toSpecCtx, fcfg'.toSpecCtx, fstep with
--   | ⟨locs, lbls, i, .(i)⟩
--   , ⟨.(locs), .(lbls), .(i), .(i)⟩
--   , ⟨ls, lstk, vs, .(.seq .nop _)⟩
--   , ⟨.(ls), .(lstk), .(vs), .(.seq .nop _)⟩
--   , ⟨.(locs), .(lbls), .(i), .(i)⟩
--   , ⟨.(locs), .(lbls), .(i), .(i)⟩
--   , .fstep_nop
--     => .sstep_nop
--   | _, _, _, _, _ => sorry

-- inductive Equiv :
--   (fctx  : FastCtx) ->
--   (fctx' : FastCtx) ->
--   (fcfg  : FastConfig fctx ) ->
--   (fcfg' : FastConfig fctx') ->

--   (sctx  : SpecCtx) ->
--   (sctx' : SpecCtx) ->
--   (scfg  : SConfig sctx ) ->
--   (scfg' : SConfig sctx') ->

--   (hargs  : sctx  = fcfg.toSpecCtx ) ->
--   (hargs' : sctx' = fcfg'.toSpecCtx) ->
--   (hcfg  : scfg  = by rw [hargs];  exact fcfg.toSpec ) ->
--   (hcfg' : scfg' = by rw [hargs']; exact fcfg'.toSpec) ->

--   (fstep  : FastStep  fctx fctx' fcfg fcfg') ->
--   (sstep  : SStep  sctx sctx' scfg scfg') ->
--   Type
-- where
--   | equiv_nop : Equiv ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨ls, lstk, vs, .seq .nop es⟩ ⟨ls, lstk, vs, es⟩ ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨ls, vs, .seq .nop es.toSpec⟩ ⟨ls, vs, es.toSpec⟩ _ _ _ _ .fstep_nop .sstep_nop

-- def equiv_fstep_sstep
--   (fctx : FastCtx) (fcfg : FastConfig fctx) (fctx' : FastCtx) (fcfg' : FastConfig fctx')
--   (h : fast_eval fcfg = ⟨fctx', fcfg'⟩)
--   : eval_sstep fcfg.toSpec = ⟨fcfg'.toSpecCtx, fcfg'.toSpec⟩
-- := by
--   sorry
