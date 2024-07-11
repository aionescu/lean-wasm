import LeanWasm.HList
import LeanWasm.Syntax.Instr
import LeanWasm.Eval.Fast

open Instrs.Notation

def run_example (es : Instrs .src locs [] i o) (vs : Stack i) : Option (Σ o', Stack o') :=
  let ⟨_, fcfg⟩ := (FastConfig.mk (c := ⟨locs, [], i, o⟩) default default .empty vs es.toFast).evals 1000

  if fcfg.isTrap then
    none
  else
    some ⟨_, fcfg.vs⟩

def print_example (name : String) (es : Instrs .src locs [] i o) (vs : Stack i) : IO Unit := do
  IO.print (name ++ ": ")

  match run_example es vs with
  | none => IO.println "Execution trapped."
  | some ⟨_, vs⟩ => IO.println vs

def unreachable : Instrs .src [] [] [] [] :=
  .unreachable; .done

def simple_add : Instrs .src [] [] [] [.i32] :=
  .const 1;
  .const 2;
  .const 3;
  .i_binop .add;
  .i_binop .add;
  .done

def locals_simple : Instrs .src [.i32] [] [] [.i32, .i32] :=
  .local_get 0;
  .const (t := .i32) 5;
  .local_set 0;
  .local_get 0;
  .done

def factorial : Instrs .src [.i32] [] [.i32] [.i32] :=
  .local_set 0;
  .const 1;
  .block (i := [.i32]) (o := [.i32]) (
    .loop (i := [.i32]) (o := [.i32]) (
      .local_get (t := .i32) 0;
      .const 0;
      .i_relop (.le .s);
      .br_if (.miss .hit);

      .local_get 0;
      .local_get 0;
      .const 1;
      .i_binop .sub;
      .local_set (t := .i32) 0;
      .i_binop .mul;

      .br .hit;
      .done
    );
    .done
  );
  .done

def memory_simple : Instrs .src [] [] [] [.i64, .i32] :=
  .const 8;
  .memory_grow;

  .const 0;
  .const 1005;
  .i_store (s := 64);

  .const 0;
  .i_load (s := 64);
  .done

def memory_trap : Instrs .src [] [] [] [.i64, .i32] :=
  .const 5; -- Oops, not enough for an i64
  .memory_grow;

  .const 0;
  .const 1005;
  .i_store (s := 64);

  .const 0;
  .i_load (s := 64);
  .done
