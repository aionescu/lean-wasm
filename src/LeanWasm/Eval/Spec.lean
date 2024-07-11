import LeanWasm.HList
import LeanWasm.Syntax.Instr
import LeanWasm.Eval.Common

@[pp_using_anonymous_constructor]
structure SpecConfig (c : Context) where
  mem : Memory
  ls : Stack c.locs
  vs : Stack c.i
  es : Instrs .spec c.locs c.lbls c.i c.o

inductive SpecStep :
  (ctx  : Context) ->
  (ctx' : Context) ->
  SpecConfig ctx   ->
  SpecConfig ctx'  ->
  Type
where
  | sstep_nop : SpecStep ⟨locs, lbls, i, i⟩ ⟨locs, lbls, i, i⟩ ⟨mem, ls, vs, .seq .nop es⟩ ⟨mem, ls, vs, es⟩
  | sstep_unreachable : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs, .seq .unreachable es⟩ ⟨mem, ls, vs, .seq .trapping es⟩

  | sstep_drop : SpecStep ⟨locs, lbls, _ :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons a vs, .seq .drop es⟩ ⟨mem, ls, vs, es⟩
  | sstep_const : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, t :: i, o⟩ ⟨mem, ls, vs, .seq (.const a) es⟩ ⟨mem, ls, .cons a vs, es⟩

  | sstep_i_binop : SpecStep ⟨locs, lbls, .i s :: .i s :: i, o⟩ ⟨locs, lbls, .i s :: i, o⟩ ⟨mem, ls, .cons b (.cons a vs), .seq (.i_binop op) es⟩ ⟨mem, ls, .cons (op.eval a b) vs, es⟩
  | sstep_i_testop : SpecStep ⟨locs, lbls, .i s :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, .cons a vs, .seq (.i_testop op) es⟩ ⟨mem, ls, .cons (op.eval a) vs, es⟩
  | sstep_i_relop : SpecStep ⟨locs, lbls, .i s :: .i s :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, .cons b (.cons a vs), .seq (.i_relop op) es⟩ ⟨mem, ls, .cons (op.eval a b) vs, es⟩

  | sstep_f_unop : SpecStep ⟨locs, lbls, .f64 :: i, o⟩ ⟨locs, lbls, .f64 :: i, o⟩ ⟨mem, ls, .cons a vs, .seq (.f_unop op) es⟩ ⟨mem, ls, .cons (op.eval a) vs, es⟩
  | sstep_f_binop : SpecStep ⟨locs, lbls, .f64 :: .f64 :: i, o⟩ ⟨locs, lbls, .f64 :: i, o⟩ ⟨mem, ls, .cons b (.cons a vs), .seq (.f_binop op) es⟩ ⟨mem, ls, .cons (op.eval a b) vs, es⟩
  | sstep_f_relop : SpecStep ⟨locs, lbls, .f64 :: .f64 :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, .cons b (.cons a vs), .seq (.f_relop op) es⟩ ⟨mem, ls, .cons (op.eval a b) vs, es⟩

  | sstep_local_get : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, _ :: i, o⟩ ⟨mem, ls, vs, .seq (.local_get ix) es⟩ ⟨mem, ls, .cons (ls.get ix) vs, es⟩
  | sstep_local_set : SpecStep ⟨locs, lbls, _ :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons a vs, .seq (.local_set ix) es⟩ ⟨mem, ls.set ix a, vs, es⟩
  | sstep_local_tee : SpecStep ⟨locs, lbls, t :: i, o⟩ ⟨locs, lbls, t :: i, o⟩ ⟨mem, ls, .cons a vs, .seq (.local_tee ix) es⟩ ⟨mem, ls.set ix a, .cons a vs, es⟩

  | sstep_memory_size : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, vs, .seq .memory_size es⟩ ⟨mem, ls, .cons mem.size vs, es⟩

  | sstep_memory_grow_trap : mem.grow a = none -> SpecStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons a vs, .seq .memory_grow es⟩ ⟨mem, ls, vs, .seq .trapping es⟩
  | sstep_memory_grow_ok : mem.grow a = some mem' -> SpecStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, .i32 :: i, o⟩ ⟨mem, ls, .cons a vs, .seq .memory_grow es⟩ ⟨mem', ls, .cons mem'.size vs, es⟩

  | sstep_i_load_trap : mem.loadILittleEndian addr = none -> SpecStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons addr vs, .seq .i_load es⟩ ⟨mem, ls, vs, .seq .trapping es⟩
  | sstep_i_load_ok : mem.loadILittleEndian addr = some (α := Ty.i s) a -> SpecStep ⟨locs, lbls, .i32 :: i, o⟩ ⟨locs, lbls, .i s :: i, o⟩ ⟨mem, ls, .cons addr vs, .seq .i_load es⟩ ⟨mem, ls, .cons a vs, es⟩

  | sstep_i_store_trap : mem.storeILittleEndian addr a = none -> SpecStep ⟨locs, lbls, .i s :: .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons a (.cons addr vs), .seq .i_store es⟩ ⟨mem, ls, vs, .seq .trapping es⟩
  | sstep_i_store_ok : mem.storeILittleEndian addr a = some mem' -> SpecStep ⟨locs, lbls, .i s :: .i32 :: i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, .cons a (.cons addr vs), .seq .i_store es⟩ ⟨mem', ls, vs, es⟩

  | sstep_block : SpecStep ⟨locs, lbls, i' ++ i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs' ++ vs, .seq (.block es') es⟩ ⟨mem, ls, vs, .seq (.label (λ _ => .nop)      vs' es') es⟩
  | sstep_loop  : SpecStep ⟨locs, lbls, i' ++ i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs' ++ vs, .seq (.loop  es') es⟩ ⟨mem, ls, vs, .seq (.label (λ _ => .loop es') vs' es') es⟩

  | sstep_br : SpecStep ⟨locs, lbls, i' ++ i, o⟩ ⟨locs, lbls, i' ++ i, o⟩ ⟨mem, ls, vs, .seq (.br ix) es⟩ ⟨mem, ls, vs, .seq (.breaking ix vs) es⟩
  | sstep_br_if_false : SpecStep ⟨locs, lbls, .i32 :: i ++ i', o⟩ ⟨locs, lbls, i ++ i', o⟩ ⟨mem, ls, List.cons_append _ _ _ ▸ .cons 0 vs, .seq (.br_if ix) es⟩ ⟨mem, ls, vs, es⟩
  | sstep_br_if_true  : SpecStep ⟨locs, lbls, .i32 :: i ++ i', o⟩ ⟨locs, lbls, i ++ i', o⟩ ⟨mem, ls, List.cons_append _ _ _ ▸ .cons n vs, .seq (.br_if ix) es⟩ ⟨mem, ls, vs, .seq (.br ix) es⟩

  | sstep_label_done          : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i' ++ i, o⟩ ⟨mem, ls, vs, .seq (.label k vs' .done                           )       es⟩ ⟨mem, ls, vs' ++ vs,          es⟩
  | sstep_label_breaking_hit  : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i' ++ i, o⟩ ⟨mem, ls, vs, .seq (.label k vs' (.seq (.breaking .hit vs'') es'))       es⟩ ⟨mem, ls, vs''.take _ ++ vs, .seq (k _) es⟩
  | sstep_label_breaking_miss : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i,       o⟩ ⟨mem, ls, vs, .seq (.label k vs' (.seq (.breaking (.miss ix) vs'') es')) es⟩ ⟨mem, ls, vs,                .seq (.breaking ix vs'') es⟩
  | sstep_label_trapping      : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i,       o⟩ ⟨mem, ls, vs, .seq (.label k vs' (.seq .trapping                   es')) es⟩ ⟨mem, ls, vs,                .seq .trapping es⟩

  | sstep_label_inner :
      SpecStep ⟨locs, _ :: lbls, i', o'⟩ ⟨locs, _ :: lbls, i'', o'⟩ ⟨mem, ls, vs', es'⟩ ⟨mem', ls', vs'', es''⟩ ->
      SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs, .seq (.label k vs' es') es⟩ ⟨mem', ls', vs, .seq (.label k vs'' es'') es⟩

  | sstep_done : SpecStep ⟨locs, lbls, i, i⟩ ⟨locs, lbls, i, i⟩ ⟨mem, ls, vs, .done⟩ ⟨mem, ls, vs, .done⟩

  | sstep_breaking : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs, .seq (.breaking ix vs') es⟩ ⟨mem, ls, vs, .seq (.breaking ix vs') es⟩
  | sstep_trapping : SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs, .seq .trapping es⟩ ⟨mem, ls, vs, .seq .trapping .done⟩

inductive SpecSteps :
  (ctx  : Context) ->
  (ctx' : Context) ->
  SpecConfig ctx   ->
  SpecConfig ctx'  ->
  Type
where
  | ssteps_refl : SpecSteps ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i, o⟩ ⟨mem, ls, vs, es⟩ ⟨mem, ls, vs, es⟩
  | ssteps_trans :
      SpecStep  ⟨locs, lbls, i,  o ⟩ ⟨locs, lbls, i',  o' ⟩ ⟨mem,  ls,  vs,  es ⟩ ⟨mem',  ls',  vs',  es' ⟩ ->
      SpecSteps ⟨locs, lbls, i', o'⟩ ⟨locs, lbls, i'', o''⟩ ⟨mem', ls', vs', es'⟩ ⟨mem'', ls'', vs'', es''⟩ ->
      SpecSteps ⟨locs, lbls, i,  o ⟩ ⟨locs, lbls, i'', o''⟩ ⟨mem,  ls,  vs,  es ⟩ ⟨mem'', ls'', vs'', es''⟩

def isFinal_unpacked
  (_mem : Memory) (_ls : Stack locs) (_vs : Stack i) (es : Instrs .spec locs lbls i o)
  : Bool
:=
  match es with
  | .done => true
  | .seq .trapping _ => true
  | _ => false

def SpecConfig.isFinal (cfg : SpecConfig ctx) : Bool :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ => isFinal_unpacked mem ls vs es

def SpecConfig.isTrap_unpacked
  (_mem : Memory) (_ls : Stack locs) (_vs : Stack i) (es : Instrs .spec locs lbls i o)
  : Bool
:=
  match es with
  | .seq .trapping _ => true
  | _ => false

def SpecConfig.isTrap (cfg : SpecConfig ctx) : Bool :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ => SpecConfig.isTrap_unpacked mem ls vs es

def SpecConfig.eval_unpacked
  (mem : Memory) (ls : Stack locs) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  : Σ i', Memory × Stack locs × Stack i' × Instrs .spec locs lbls i' o
:=
  match es with
  | .done => ⟨_, mem, ls, vs, .done⟩
  | .seq e es =>
      match e, vs with
      | .nop, vs => ⟨_, mem, ls, vs, es⟩
      | .unreachable, vs => ⟨_, mem, ls, vs, .seq .trapping es⟩

      | .drop, .cons _ vs => ⟨_, mem, ls, vs, es⟩
      | .const a, vs => ⟨_, mem, ls, .cons a vs, es⟩

      | .i_binop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es⟩
      | .i_testop op, .cons a vs => ⟨_, mem, ls, .cons (op.eval a) vs, es⟩
      | .i_relop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es⟩

      | .f_unop op, .cons a vs => ⟨_, mem, ls, .cons (op.eval a) vs, es⟩
      | .f_binop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es⟩
      | .f_relop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es⟩

      | .local_get ix, vs => ⟨_, mem, ls, .cons (ls.get ix) vs, es⟩
      | .local_set ix, .cons a vs => ⟨_, mem, ls.set ix a, vs, es⟩
      | .local_tee ix, .cons a vs => ⟨_, mem, ls.set ix a, .cons a vs, es⟩

      | .memory_size, vs => ⟨_, mem, ls, .cons mem.size vs, es⟩
      | .memory_grow, .cons a vs =>
          match mem.grow a with
          | none => ⟨_, mem, ls, vs, .seq .trapping es⟩
          | some mem' => ⟨_, mem', ls, .cons mem'.size vs, es⟩

      | .i_load, .cons addr vs =>
          match mem.loadILittleEndian addr with
          | none => ⟨_, mem, ls, vs, .seq .trapping es⟩
          | some a => ⟨_, mem, ls, .cons a vs, es⟩

      | .i_store, .cons a (.cons addr vs) =>
          match mem.storeILittleEndian addr a with
          | none => ⟨_, mem, ls, vs, .seq .trapping es⟩
          | some mem' => ⟨_, mem', ls, vs, es⟩

      | .block es', vs => ⟨_, mem, ls, (vs.drop _), .seq (.label (λ _ => .nop (knd := .spec)) (vs.take _) es') es⟩
      | .loop es',  vs => ⟨_, mem, ls, (vs.drop _), .seq (.label (λ _ => .loop es') (vs.take _) es') es⟩

      | .br ix, vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs) es⟩

      | .br_if ix, .cons v vs =>
          match v with
          | 0 => ⟨_, mem, ls, vs, es⟩
          | _ => ⟨_, mem, ls, vs, .seq (.br ix) es⟩

      | .label _k vs' .done, vs => ⟨_, mem, ls, vs' ++ vs, es⟩

      | .label k _vs' (.seq (.breaking .hit vs'') es'), vs => ⟨_, mem, ls, vs''.take _ ++ vs, .seq (k _) es⟩
      | .label _k _vs' (.seq (.breaking (.miss ix) vs'') es'), vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs'') es⟩

      | .label k vs' es', vs =>
          let ⟨_, mem', ls', vs'', es''⟩ := SpecConfig.eval_unpacked mem ls vs' es'
          ⟨_, mem', ls', vs, .seq (.label k vs'' es'') es⟩

      | .breaking ix vs', vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs') es⟩
      | .trapping, vs => ⟨_, mem, ls, vs, .seq .trapping .done⟩

def SpecConfig.evals_unpacked
  (mem : Memory) (ls : Stack locs) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  (fuel : Nat)
  : Σ i', Memory × Stack locs × Stack i' × Instrs .spec locs lbls i' o
:=
  match fuel with
  | 0 => ⟨_, mem, ls, vs, es⟩
  | fuel + 1 =>
      if isFinal_unpacked mem ls vs es then
        ⟨_, mem, ls, vs, es⟩
      else
        let ⟨_, mem', ls', vs', es'⟩ := SpecConfig.eval_unpacked mem ls vs es
        SpecConfig.evals_unpacked mem' ls' vs' es' fuel

def SpecConfig.eval (cfg : SpecConfig ctx) : Σ ctx', SpecConfig ctx' :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ =>
      match SpecConfig.eval_unpacked mem ls vs es with
      | ⟨i', mem', ls', vs', es'⟩ => ⟨⟨ctx.locs, ctx.lbls, i', ctx.o⟩, ⟨mem', ls', vs', es'⟩⟩

def SpecConfig.evals (cfg : SpecConfig ctx) (fuel : Nat) : Σ ctx', SpecConfig ctx' :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ =>
      match SpecConfig.evals_unpacked mem ls vs es fuel with
      | ⟨i', mem', ls', vs', es'⟩ => ⟨⟨ctx.locs, ctx.lbls, i', ctx.o⟩, ⟨mem', ls', vs', es'⟩⟩

def SpecConfig.eval_unpacked_proofCarrying
  {locs : List Ty} {lbls : List (List Ty)} {i o : List Ty}
  (mem : Memory) (ls : Stack locs) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  : Σ i', (mem' : Memory) × (ls' : Stack locs) × (vs' : Stack i') × (es' : Instrs .spec locs lbls i' o) × SpecStep ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i', o⟩ ⟨mem, ls, vs, es⟩ ⟨mem', ls', vs', es'⟩
:=
  match locs, lbls, i, o, es with
  | _, _, _, _, .done => ⟨_, mem, ls, vs, .done, .sstep_done⟩
  | locs, lbls, i, o, .seq (i := .(i)) (o := o') (o' := .(o)) e es =>
      match i, o', o, e, vs with
      | _, _, _, .nop, vs => ⟨_, mem, ls, vs, es, sorry⟩ -- .sstep_nop⟩
      | _, _, _, .unreachable, vs => ⟨_, mem, ls, vs, .seq .trapping es, .sstep_unreachable⟩

      | _, _, _, .drop, .cons _ vs => ⟨_, mem, ls, vs, es, .sstep_drop⟩
      | _, _, _, .const a, vs => ⟨_, mem, ls, .cons a vs, es, .sstep_const⟩

      | _, _, _, .i_binop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es, .sstep_i_binop⟩
      | _, _, _, .i_testop op, .cons a vs => ⟨_, mem, ls, .cons (op.eval a) vs, es, .sstep_i_testop⟩
      | _, _, _, .i_relop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es, .sstep_i_relop⟩

      | _, _, _, .f_unop op, .cons a vs => ⟨_, mem, ls, .cons (op.eval a) vs, es, .sstep_f_unop⟩
      | _, _, _, .f_binop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es, .sstep_f_binop⟩
      | _, _, _, .f_relop op, .cons b (.cons a vs) => ⟨_, mem, ls, .cons (op.eval a b) vs, es, .sstep_f_relop⟩

      | _, _, _, .local_get ix, vs => ⟨_, mem, ls, .cons (ls.get ix) vs, es, .sstep_local_get⟩
      | _, _, _, .local_set ix, .cons a vs => ⟨_, mem, ls.set ix a, vs, es, .sstep_local_set⟩
      | _, _, _, .local_tee ix, .cons a vs => ⟨_, mem, ls.set ix a, .cons a vs, es, .sstep_local_tee⟩

      | _, _, _, .memory_size, vs => ⟨_, mem, ls, .cons mem.size vs, es, .sstep_memory_size⟩
      | _, _, _, .memory_grow, .cons a vs =>
          match h : mem.grow a with
          | none => ⟨_, mem, ls, vs, .seq .trapping es, .sstep_memory_grow_trap h⟩
          | some mem' => ⟨_, mem', ls, .cons mem'.size vs, es, .sstep_memory_grow_ok h⟩

      | _, _, _, .i_load, .cons addr vs =>
          match h : mem.loadILittleEndian addr with
          | none => ⟨_, mem, ls, vs, .seq .trapping es, .sstep_i_load_trap h⟩
          | some a => ⟨_, mem, ls, .cons a vs, es, .sstep_i_load_ok h⟩

      | _, _, _, .i_store, .cons a (.cons addr vs) =>
          match h : mem.storeILittleEndian addr a with
          | none => ⟨_, mem, ls, vs, .seq .trapping es, .sstep_i_store_trap h⟩
          | some mem' => ⟨_, mem', ls, vs, es, .sstep_i_store_ok h⟩

      | _, _, _, .block es', vs => ⟨_, mem, ls, (vs.drop _), .seq (.label (λ _ => .nop (knd := .spec)) (vs.take _) es') es, sorry⟩ -- .sstep_block⟩
      | _, _, _, .loop es',  vs => ⟨_, mem, ls, (vs.drop _), .seq (.label (λ _ => .loop es') (vs.take _) es') es, sorry⟩ -- .sstep_loop⟩

      | _, _, _, .br ix, vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs) es, .sstep_br⟩

      | _, _, _, .br_if ix, .cons v vs =>
          match v with
          | 0 => ⟨_, mem, ls, vs, es, .sstep_br_if_false⟩
          | _ => ⟨_, mem, ls, vs, .seq (.br ix) es, .sstep_br_if_true⟩

      | _, _, _, .label _k vs' .done, vs => ⟨_, mem, ls, vs' ++ vs, es, .sstep_label_done⟩

      | _, _, _, .label k _vs' (.seq (.breaking .hit vs'') es'), vs => ⟨_, mem, ls, vs''.take _ ++ vs, .seq (k _) es, .sstep_label_breaking_hit⟩
      | _, _, _, .label _k _vs' (.seq (.breaking (.miss ix) vs'') es'), vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs'') es, .sstep_label_breaking_miss⟩

      | _, _, _, .label k vs' es', vs =>
          let ⟨_, mem', ls', vs'', es'', sstep⟩ := SpecConfig.eval_unpacked_proofCarrying mem ls vs' es'
          ⟨_, mem', ls', vs, .seq (.label k vs'' es'') es, .sstep_label_inner sstep⟩

      | _, _, _, .breaking ix vs', vs => ⟨_, mem, ls, vs, .seq (.breaking ix vs') es, .sstep_breaking⟩
      | _, _, _, .trapping, vs => ⟨_, mem, ls, vs, .seq .trapping .done, .sstep_trapping⟩

def SpecConfig.evals_unpacked_proofCarrying
  {locs : List Ty} {lbls : List (List Ty)} {i o : List Ty}
  (mem : Memory) (ls : Stack locs) (vs : Stack i) (es : Instrs .spec locs lbls i o)
  (fuel : Nat)
  : Σ i', (mem' : Memory) × (ls' : Stack locs) × (vs' : Stack i') × (es' : Instrs .spec locs lbls i' o) × SpecSteps ⟨locs, lbls, i, o⟩ ⟨locs, lbls, i', o⟩ ⟨mem, ls, vs, es⟩ ⟨mem', ls', vs', es'⟩
:=
  match fuel with
  | 0 => ⟨_, mem, ls, vs, es, .ssteps_refl⟩
  | fuel + 1 =>
      if isFinal_unpacked mem ls vs es then
        ⟨_, mem, ls, vs, es, .ssteps_refl⟩
      else
        let ⟨_, mem', ls', vs', es', sstep⟩ := SpecConfig.eval_unpacked_proofCarrying mem ls vs es
        let ⟨_, mem'', ls'', vs'', es'', ssteps⟩ := SpecConfig.evals_unpacked_proofCarrying mem' ls' vs' es' fuel
        ⟨_, mem'', ls'', vs'', es'', .ssteps_trans sstep ssteps⟩

def SpecConfig.eval_proofCarrying (cfg : SpecConfig ctx) : Σ ctx', (cfg' : SpecConfig ctx') × SpecStep ctx ctx' cfg cfg' :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ =>
      match SpecConfig.eval_unpacked_proofCarrying mem ls vs es with
      | ⟨i', mem', ls', vs', es', sstep⟩ => ⟨⟨ctx.locs, ctx.lbls, i', ctx.o⟩, ⟨mem', ls', vs', es'⟩, sstep⟩

def SpecConfig.evals_proofCarrying (cfg : SpecConfig ctx) (fuel : Nat) : Σ ctx', (cfg' : SpecConfig ctx') × SpecSteps ctx ctx' cfg cfg' :=
  match cfg with
  | ⟨mem, ls, vs, es⟩ =>
      match SpecConfig.evals_unpacked_proofCarrying mem ls vs es fuel with
      | ⟨i', mem', ls', vs', es', ssteps⟩ => ⟨⟨ctx.locs, ctx.lbls, i', ctx.o⟩, ⟨mem', ls', vs', es'⟩, ssteps⟩
