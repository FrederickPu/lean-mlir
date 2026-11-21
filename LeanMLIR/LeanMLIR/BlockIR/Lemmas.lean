/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Core
import LeanMLIR.BlockIR.SimpSet

/-!
# Reasoning principles for `Block.eval`

Lemmas *about* the trusted interpreter in `Core.lean`, proved from its
`partial_fixpoint` equation. Nothing here is trusted.

`Block.eval_of_noCall`: a block without `call`s runs its instructions in order,
which `straight` spells out (it is a proof device, characterised by that lemma).
-/

namespace OpAlgebra
variable {opAlg : OpAlgebra}

/-- Bind `pairs` into `env`, exactly as the `for` loops in `Block.eval` do. -/
def bindPairs (env : Std.HashMap String opAlg.Data) (pairs : List (String × opAlg.Data)) :
    Std.HashMap String opAlg.Data :=
  pairs.foldl (fun e p => e.insert p.1 p.2) env

/-- Run call-free instructions in order (see `Block.eval_of_noCall`). -/
def straight (callStack : List Nat) :
    Std.HashMap String opAlg.Data → opAlg.State → List opAlg.Instruction →
    Option opAlg.BlockResult
  | _, s, [] => some ⟨callStack.dropLast, [opAlg.novalue], s⟩
  | env, s, instr :: rest => do
    let inputs ← instr.args.mapM (·.instantiate env)
    match instr.op with
    | .ofPrimOp p =>
      let (retVals, s') ← opAlg.eval p s inputs
      let pairs ← instr.registers.zip? retVals
      straight callStack (bindPairs env pairs) s' rest
    | .ret target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      some ⟨callStack.dropFromLast i, inputs, s⟩
    | .call _ => none

/-- An instruction list without `call`s. -/
def NoCall (instrs : List opAlg.Instruction) : Prop :=
  ∀ i ∈ instrs, ∀ t, i.op ≠ .call t

theorem forIn_insert (pairs : List (String × opAlg.Data)) (env : Std.HashMap String opAlg.Data) :
    (forIn pairs env fun x r => some (ForInStep.yield (r.insert x.fst x.snd))) =
      some (bindPairs env pairs) := by
  induction pairs generalizing env with
  | nil => rfl
  | cons p ps ih => simp [List.forIn_cons, bindPairs, ih]

theorem Block.eval_of_noCall (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (block : Block opAlg) (args : List opAlg.Data) (h : NoCall block.instructions) :
    Block.eval blocks state env callStack block args =
      ((block.args.zip? args).bind fun pairs =>
        straight callStack (bindPairs env pairs) state block.instructions) := by
  rw [Block.eval.eq_1]
  rcases block with ⟨bargs, instrs⟩
  simp only at h ⊢
  rcases (bargs.zip? args) with _ | pairs
  · rfl
  simp [forIn_insert]
  generalize bindPairs env pairs = e
  induction instrs generalizing e state with
  | nil => simp [straight]
  | cons i is ih =>
    have hi : ∀ t, i.op ≠ .call t := h i (by simp)
    have h' : NoCall is := fun j hj => h j (by simp [hj])
    rcases i with ⟨regs, op, iargs⟩
    cases op with
    | call t => exact absurd rfl (hi t)
    | ret t =>
      simp only [straight, List.forIn_cons]
      cases (List.mapM (fun x => x.instantiate e) iargs) <;> simp
      cases t.instantiate e <;> simp
      cases opAlg.toBlockIdx? _ <;> simp
    | ofPrimOp p =>
      simp only [straight, List.forIn_cons]
      cases (List.mapM (fun x => x.instantiate e) iargs) <;> simp
      cases opAlg.eval p state _ <;> simp
      cases regs.zip? _ <;> simp
      exact ih _ h' _


@[simp] theorem bindPairs_nil (env : Std.HashMap String opAlg.Data) : bindPairs env [] = env := rfl

@[simp] theorem bindPairs_cons (env : Std.HashMap String opAlg.Data) (p) (ps) :
    bindPairs env (p :: ps) = bindPairs (env.insert p.1 p.2) ps := rfl

/-- `simp` forms of `bindPairs_nil`/`bindPairs_cons` that also fire when the list's element
type has been unfolded (e.g. to the dialect's `Data`). -/
@[simp, block_eval] theorem bindPairs_nil' (env : Std.HashMap String opAlg.Data) :
    bindPairs env (no_index []) = env := rfl
@[simp, block_eval] theorem bindPairs_cons' (env : Std.HashMap String opAlg.Data) (p) (ps) :
    bindPairs env (no_index (p :: ps)) = bindPairs (env.insert p.1 p.2) ps := rfl

theorem bindPairs_getElem?_of_not_mem {env : Std.HashMap String opAlg.Data} {ps} {k : String}
    (h : k ∉ ps.map Prod.fst) : (bindPairs env ps)[k]? = env[k]? := by
  induction ps generalizing env with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [bindPairs_cons, ih h.2, Std.HashMap.getElem?_insert]
    simp [Ne.symm h.1]

theorem bindPairs_getElem?_of_mem {env : Std.HashMap String opAlg.Data} {ps} {k : String} {v}
    (hnd : (ps.map Prod.fst).Nodup) (h : (k, v) ∈ ps) : (bindPairs env ps)[k]? = some v := by
  induction ps generalizing env with
  | nil => simp at h
  | cons p ps ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [bindPairs_cons]
    rcases List.mem_cons.1 h with rfl | h
    · rw [bindPairs_getElem?_of_not_mem hnd.1, Std.HashMap.getElem?_insert]; simp
    · exact ih hnd.2 h


/-! ## Splitting a block at a call-free prefix -/

/-- Run a call-free prefix: either it returns (`inl`), or it falls through to the rest of
the block with a new environment and state (`inr`). -/
def runPrefix (callStack : List Nat) :
    Std.HashMap String opAlg.Data → opAlg.State → List opAlg.Instruction →
    Option (opAlg.BlockResult ⊕ (Std.HashMap String opAlg.Data × opAlg.State))
  | env, s, [] => some (.inr (env, s))
  | env, s, instr :: rest => do
    let inputs ← instr.args.mapM (·.instantiate env)
    match instr.op with
    | .ofPrimOp p =>
      let (retVals, s') ← opAlg.eval p s inputs
      let pairs ← instr.registers.zip? retVals
      runPrefix callStack (bindPairs env pairs) s' rest
    | .ret target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      some (.inl ⟨callStack.dropFromLast i, inputs, s⟩)
    | .call _ => none

/-- Continue after a prefix: a `ret` ends the block, otherwise run the rest. -/
def afterPrefix (blocks : List (Block opAlg)) (callStack : List Nat) (rest : List opAlg.Instruction) :
    opAlg.BlockResult ⊕ (Std.HashMap String opAlg.Data × opAlg.State) → Option opAlg.BlockResult
  | .inl r => some r
  | .inr (env, s) => Block.eval blocks s env callStack ⟨[], rest⟩ []

theorem runPrefix_append (callStack : List Nat) (env : Std.HashMap String opAlg.Data)
    (s : opAlg.State) (xs ys : List opAlg.Instruction) :
    runPrefix callStack env s (xs ++ ys) =
      (runPrefix callStack env s xs).bind fun
        | .inl r => some (.inl r)
        | .inr (env', s') => runPrefix callStack env' s' ys := by
  induction xs generalizing env s with
  | nil => simp [runPrefix]
  | cons i is ih =>
    rcases i with ⟨regs, op, iargs⟩
    simp only [List.cons_append, runPrefix]
    cases (List.mapM (fun x => x.instantiate env) iargs) <;> simp
    cases op with
    | call t => simp
    | ret t =>
      simp
      cases t.instantiate env <;> simp
      cases opAlg.toBlockIdx? _ <;> simp
    | ofPrimOp p =>
      simp
      cases opAlg.eval p s _ <;> simp
      cases regs.zip? _ <;> simp [ih]

/-- **Splitting**: a block whose instructions start with a call-free prefix `pre` runs
`pre` first, then the rest of the block from the resulting environment and state. -/
theorem Block.eval_append (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat) (bargs : List String)
    (pre rest : List opAlg.Instruction) (args : List opAlg.Data) (h : NoCall pre) :
    Block.eval blocks state env callStack ⟨bargs, pre ++ rest⟩ args =
      ((bargs.zip? args).bind fun pairs =>
        (runPrefix callStack (bindPairs env pairs) state pre).bind
          (afterPrefix blocks callStack rest)) := by
  conv => lhs; rw [Block.eval.eq_1]
  rcases (bargs.zip? args) with _ | pairs
  · rfl
  simp [forIn_insert]
  generalize bindPairs env pairs = e
  induction pre generalizing e state with
  | nil =>
    simp only [runPrefix, Option.bind_some, afterPrefix]
    rw [Block.eval.eq_1]
    simp [List.zip?, forIn_insert, bindPairs]
  | cons i is ih =>
    have hi : ∀ t, i.op ≠ .call t := h i (by simp)
    have h' : NoCall is := fun j hj => h j (by simp [hj])
    rcases i with ⟨regs, op, iargs⟩
    cases op with
    | call t => exact absurd rfl (hi t)
    | ret t =>
      simp only [runPrefix, List.cons_append, List.forIn_cons]
      cases (List.mapM (fun x => x.instantiate e) iargs) <;> simp
      cases t.instantiate e <;> simp
      cases opAlg.toBlockIdx? _ <;> simp [afterPrefix]
    | ofPrimOp p =>
      simp only [runPrefix, List.cons_append, List.forIn_cons]
      cases (List.mapM (fun x => x.instantiate e) iargs) <;> simp
      cases opAlg.eval p state _ <;> simp
      cases regs.zip? _ <;> simp
      exact ih _ h' _

/-! ## Block arguments, `call`, and `ret` -/

/-- Binding a block's arguments is the same as extending the environment and running
an argument-free block. -/
theorem Block.eval_args (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat) (bargs : List String)
    (instrs : List opAlg.Instruction) (args : List opAlg.Data) :
    Block.eval blocks state env callStack ⟨bargs, instrs⟩ args =
      (bargs.zip? args).bind fun pairs =>
        Block.eval blocks state (bindPairs env pairs) callStack ⟨[], instrs⟩ [] := by
  have h1 := Block.eval_append blocks state env callStack bargs [] instrs args
    (by intro i hi; simp at hi)
  rw [List.nil_append] at h1
  rw [h1]
  congr 1

/-- **`call`**: run the callee with the caller's environment and the callee's label
pushed on the call stack. If the callee's `ret` unwinds past us, propagate; otherwise
bind its results and continue. -/
@[block_eval] theorem Block.eval_call (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (target : opAlg.Arg) (cargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval blocks state env callStack ⟨[], ⟨regs, .call target, cargs⟩ :: rest⟩ noargs =
      ((cargs.mapM (fun a : opAlg.Arg => a.instantiate env)).bind fun inputs =>
        (target.instantiate env).bind fun t =>
        (opAlg.toBlockIdx? t).bind fun i =>
        blocks[i]?.bind fun b =>
        (b.eval blocks state env (callStack ++ [i]) inputs).bind fun r =>
          if r.callStack.length < callStack.length then some r
          else (regs.zip? r.retVals).bind fun pairs =>
            Block.eval blocks r.state (bindPairs env pairs) callStack ⟨[], rest⟩ []) := by
  subst hno
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) cargs with _ | inputs <;>
    conv => lhs; rw [Block.eval.eq_1]
  · simp [List.zip?, forIn_insert, bindPairs, hm]
  rcases ht : target.instantiate env with _ | t
  · simp [List.zip?, forIn_insert, bindPairs, hm, ht]
  rcases hi : opAlg.toBlockIdx? t with _ | i
  · simp [List.zip?, forIn_insert, bindPairs, hm, ht, hi]
  rcases hb : blocks[i]? with _ | b
  · simp [List.zip?, forIn_insert, bindPairs, hm, ht, hi, hb]
  rcases hr : b.eval blocks state env (callStack ++ [i]) inputs with _ | r
  · simp [List.zip?, forIn_insert, bindPairs, hm, ht, hi, hb, hr]
  simp only [List.zip?, List.length_nil, beq_self_eq_true, if_true, List.zip_nil_left,
    Option.bind_some, Option.bind_eq_bind, hm, ht, hi, hb, hr]
  simp [forIn_insert, bindPairs, hm, ht, hi, hb, hr]
  split
  · simp
  rcases hz : regs.zip? r.retVals with _ | pairs
  · simp [List.zip?] at hz ⊢; simp [hz]
  simp [List.zip?] at hz ⊢
  obtain ⟨hlen, rfl⟩ := hz
  simp only [hlen, if_true, Option.bind_some]
  rw [Block.eval.eq_1 blocks _ _ callStack ⟨[], rest⟩ []]
  simp [List.zip?, forIn_insert, bindPairs]

/-- **`ret`**: return the arguments, unwinding the call stack to the latest call of
the target block. -/
@[block_eval] theorem Block.eval_ret (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (target : opAlg.Arg) (rargs : List opAlg.Arg) (rest : List opAlg.Instruction)
    {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval blocks state env callStack ⟨[], ⟨[], .ret target, rargs⟩ :: rest⟩ noargs =
      ((rargs.mapM (fun a : opAlg.Arg => a.instantiate env)).bind fun outs =>
        (target.instantiate env).bind fun t =>
        (opAlg.toBlockIdx? t).bind fun i =>
          some ⟨callStack.dropFromLast i, outs, state⟩) := by
  subst hno
  have h := Block.eval_append blocks state env callStack [] [⟨[], .ret target, rargs⟩] rest []
    (by intro i hi t; simp at hi; subst hi; simp)
  rw [List.singleton_append] at h
  rw [h]
  simp only [List.zip?, runPrefix]
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) rargs with _ | outs
  · simp [hm]
  rcases ht : target.instantiate env with _ | t
  · simp [hm, ht]
  rcases hi : opAlg.toBlockIdx? t with _ | i
  · simp [hm, ht, hi]
  simp [hm, ht, hi, afterPrefix]

/-- Returning from a block that was just called restores the caller's call stack. -/
@[simp, block_eval] theorem dropFromLast_append_self (cs : List Nat) (i : Nat) :
    (cs ++ [i]).dropFromLast i = cs := by
  simp [List.dropFromLast, List.findLastIdx?, List.findIdx?_cons]


/-- **One primop**: evaluate it, bind its results, and continue. -/
@[block_eval] theorem Block.eval_prim (blocks : List (Block opAlg)) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (p : opAlg.PrimOp) (pargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval blocks state env callStack ⟨[], ⟨regs, .ofPrimOp p, pargs⟩ :: rest⟩ noargs =
      ((pargs.mapM (fun a : opAlg.Arg => a.instantiate env)).bind fun inputs =>
        (opAlg.eval p state inputs).bind fun r =>
        (regs.zip? r.1).bind fun pairs =>
          Block.eval blocks r.2 (bindPairs env pairs) callStack ⟨[], rest⟩ []) := by
  subst hno
  have h := Block.eval_append blocks state env callStack [] [⟨regs, .ofPrimOp p, pargs⟩] rest []
    (by intro i hi t; simp at hi; subst hi; simp)
  rw [List.singleton_append] at h
  rw [h]
  have hnil : ([] : List String).zip? ([] : List opAlg.Data) = some [] := rfl
  simp only [hnil, Option.bind_some, bindPairs_nil, runPrefix, Option.bind_eq_bind]
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) pargs with _ | ins <;>
    simp only [hm, Option.bind_none, Option.bind_some]
  rcases he : opAlg.eval p state ins with _ | ⟨rv, s'⟩ <;>
    simp only [he, Option.bind_none, Option.bind_some]
  rcases hz : regs.zip? rv with _ | ps <;>
    simp only [hz, Option.bind_none, Option.bind_some, runPrefix, afterPrefix]

end OpAlgebra
