/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.WellScoped

/-!
# The step rules of `block_eval`

Every rule that runs an instruction is stated with `Block.seq` in place of `Option.bind`.
`Block.seq o f` is `o.bind f`, but its congruence lemma lets `simp` rewrite only `o`: the
continuation `f` (the rest of the block) is left alone until `o` is a value and
`Block.seq_some` hands it that value. So `simp` runs a block front to back, once, on
concrete environments, instead of symbolically evaluating every continuation under its
binders (which is what made plain `Option.bind` rules slow).
-/

namespace OpAlgebra
variable {opAlg : OpAlgebra}

/-- `Option.bind` that `simp` evaluates head first (see the module docstring). -/
def Block.seq {α β : Type _} (o : Option α) (f : α → Option β) : Option β := o.bind f

theorem Block.seq_congr {α β : Type _} {o o' : Option α} (h : o = o')
    (f : α → Option β) : Block.seq o f = Block.seq o' f := h ▸ rfl

open Lean Meta Simp in
/-- Evaluate `Block.seq o f` head first: simplify `o` only; on `some a` continue with
`f a`, on `none` stop with `none`, otherwise stop without entering `f`. (A `@[congr]` lemma
cannot do this: `simp` falls back to visiting every argument when it changes nothing.) -/
simproc ↓ [block_eval] seqHead (Block.seq _ _) := fun e => do
  unless e.isAppOfArity ``Block.seq 4 do return .continue
  let args := e.getAppArgs
  let f := args[3]!
  let r ← simp args[2]!
  let o' := r.expr
  let e' := mkAppN e.getAppFn #[args[0]!, args[1]!, o', f]
  let pf? ← r.proof?.mapM fun h => mkAppM ``Block.seq_congr #[h, f]
  -- `seq (some a) f` and `f a` (and `seq none f`, `none`) are definitionally equal
  let finish (res : Expr) : MetaM (Option Expr) :=
    pf?.mapM fun pf => do mkExpectedTypeHint pf (← mkEq e res)
  if o'.isAppOfArity ``Option.some 2 then
    let res := f.beta #[o'.appArg!]
    return .visit { expr := res, proof? := ← finish res }
  if o'.isAppOfArity ``Option.none 1 then
    let res ← mkAppOptM ``Option.none #[args[1]!]
    return .done { expr := res, proof? := ← finish res }
  return .done { expr := e', proof? := pf? }

@[simp, block_eval] theorem Block.seq_some {α β : Type _} (a : α) (f : α → Option β) :
    Block.seq (some a) f = f a := rfl

@[simp, block_eval] theorem Block.seq_none {α β : Type _} (f : α → Option β) :
    Block.seq none f = none := rfl

theorem Block.seq_eq_bind {α β : Type _} (o : Option α) (f : α → Option β) :
    Block.seq o f = o.bind f := rfl

/-- **One primop**: evaluate it, bind its results, and continue. -/
@[block_eval] theorem Block.step_prim (P : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (p : opAlg.PrimOp) (pargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], ⟨regs, .ofPrimOp p, pargs⟩ :: rest⟩ noargs =
      Block.seq (pargs.mapM (fun a : opAlg.Arg => a.instantiate env)) fun inputs =>
      Block.seq (opAlg.eval p state inputs) fun r =>
      Block.seq (regs.zip? r.1) fun pairs =>
        Block.eval P r.2 (bindPairs env pairs) callStack ⟨[], rest⟩ [] :=
  Block.eval_prim P state env callStack regs p pargs rest hno

/-- **Return**. -/
@[block_eval] theorem Block.step_ret (P : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (target : opAlg.Arg) (rargs : List opAlg.Arg) (rest : List opAlg.Instruction)
    {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], ⟨[], .ret target, rargs⟩ :: rest⟩ noargs =
      Block.seq (rargs.mapM (fun a : opAlg.Arg => a.instantiate env)) fun outs =>
      Block.seq (target.instantiate env) fun t =>
      Block.seq (opAlg.toBlockIdx? t) fun i =>
        some ⟨callStack.dropFromLast i, outs, state⟩ :=
  Block.eval_ret P state env callStack target rargs rest hno

/-- **End of a block**: fall through, returning `[novalue]`. -/
@[block_eval] theorem Block.step_nil (P : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat) {noargs : List opAlg.Data}
    (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], []⟩ noargs =
      some ⟨callStack.dropLast, [opAlg.novalue], state⟩ :=
  Block.eval_nil P state env callStack hno

/-- **Block arguments** (only for blocks that have some, so `simp` terminates). -/
@[block_eval] theorem Block.step_args (P : List (Block opAlg)) (s : opAlg.State)
    (e : Std.HashMap String opAlg.Data) (cs : List Nat) (a : String) (as : List String)
    (instrs : List opAlg.Instruction) (vs : List opAlg.Data) :
    Block.eval P s e cs ⟨a :: as, instrs⟩ vs =
      Block.seq ((a :: as).zip? vs) fun ps => Block.eval P s (bindPairs e ps) cs ⟨[], instrs⟩ [] :=
  Block.eval_bind_args P s e cs a as instrs vs

/-- **The gate**: in a well-scoped program a call is a function call, `Block.fn`. Not in
`block_eval` itself: `@[block_program]` adds it for each program proven well scoped. -/
theorem Block.step_call (P : List (Block opAlg)) (hws : Block.WellScoped P) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (target : opAlg.Arg) (cargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], ⟨regs, .call target, cargs⟩ :: rest⟩ noargs =
      Block.seq (cargs.mapM (fun a : opAlg.Arg => a.instantiate env)) fun inputs =>
      Block.seq (target.instantiate env) fun t =>
      Block.seq (opAlg.toBlockIdx? t) fun j =>
      Block.seq (Block.fn P j inputs state) fun r =>
      Block.seq (regs.zip? r.1) fun pairs =>
        Block.eval P r.2 (bindPairs env pairs) callStack ⟨[], rest⟩ [] :=
  Block.eval_call_ws P hws state env callStack regs target cargs rest hno

/-- **Unfold a function** (block `i` called from the top). Passed to `simp` explicitly, as
`Block.fn_step P i`, for the blocks to unfold. -/
theorem Block.fn_step (P : List (Block opAlg)) (i : Nat) (args : List opAlg.Data)
    (s : opAlg.State) :
    Block.fn P i args s =
      Block.seq P[i]? fun b =>
      Block.seq (b.args.zip? args) fun ps =>
      Block.seq (Block.eval P s (bindPairs ∅ ps) [i] ⟨[], b.instructions⟩ []) fun r =>
        if r.callStack = [] then some (r.retVals, r.state) else none :=
  Block.fn_unfold P i args s

end OpAlgebra
