/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Lemmas

/-!
# Well-scoped programs: blocks are functions

In the core, a callee runs with the caller's environment (dynamic scoping) and the
caller's call stack underneath. `Block.WellScoped P` is a decidable check that rules
out both effects, so that every `call` in `P` is a function call:

* **def-before-use**: a block only reads its own arguments and registers it bound
  earlier, never the caller's;
* **self-return**: every `ret` names the block's own label.

`Block.eval_call_wellScoped` then replaces a `call` by `Block.fn`, the callee run as a
top-level call. Higher-level IRs that lower to BlockIR can prove `WellScoped` once for
their output and pass it around.
-/

namespace OpAlgebra
variable {opAlg : OpAlgebra}

/-! ## The check -/

/-- Every register in `as` is in `D`. -/
def argsDefined (D : List String) (as : List opAlg.Arg) : Bool :=
  as.all fun | .ofVar n => D.contains n | .ofData _ => true

/-- The instructions of block `i`, with registers `D` already defined, are well scoped. -/
def instrsWellScoped (i : Nat) : List String → List opAlg.Instruction → Bool
  | _, [] => true
  | D, ins :: rest =>
    argsDefined D ins.args &&
    (match ins.op with
      | .ofPrimOp _ => true
      | .call t => argsDefined D [t]
      | .ret (.ofData l) => opAlg.toBlockIdx? l == some i
      | .ret (.ofVar _) => false) &&
    instrsWellScoped i (ins.registers ++ D) rest

/-- Every block of `P` is well scoped. -/
def Block.wellScoped (P : List (Block opAlg)) : Bool :=
  (List.range P.length).all fun i =>
    match P[i]? with
    | some b => instrsWellScoped i b.args b.instructions
    | none => true

/-- **Every block of `P` behaves like a function** (decidable). -/
abbrev Block.WellScoped (P : List (Block opAlg)) : Prop := Block.wellScoped P = true

/-- Block `i` of `P`, run as a top-level call: from an empty environment, with only
itself on the call stack, returning its results and final state. -/
def Block.fn (P : List (Block opAlg)) (i : Nat) (args : List opAlg.Data) (s : opAlg.State) :
    Option (List opAlg.Data × opAlg.State) := do
  let b ← P[i]?
  let r ← b.eval P s ∅ [i] args
  if r.callStack = [] then some (r.retVals, r.state) else none

/-! ## `Block.eval`'s body, with recursive calls going to `f` -/

/-- One unfolding of `Block.eval` (copied from `Core.lean`), calling `f` for callees. -/
def evalStep (f : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
      List opAlg.Data → Option opAlg.BlockResult)
    (blocks : List (Block opAlg))
    (state : opAlg.State) (env : Std.HashMap String opAlg.Data)
    (callStack : List Nat)
    (block : Block opAlg) (args : List opAlg.Data) :
    Option opAlg.BlockResult := do
  let mut env := env
  for (argName, argVal) in ← block.args.zip? args do
    env := env.insert argName argVal
  let mut state := state
  for instr in block.instructions do
    let inputs ← instr.args.mapM (·.instantiate env)
    let (retVals, state') ← match instr.op with
    | .call target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      let b ← blocks[i]?
      let ⟨callStack', retVals, state'⟩ ← f state env (callStack ++ [i]) b inputs
      if callStack'.length < callStack.length then
        return ⟨callStack', retVals, state'⟩
      pure (retVals, state')
    | .ret target =>
      let i ← opAlg.toBlockIdx? (← target.instantiate env)
      return ⟨callStack.dropFromLast i, inputs, state⟩
    | .ofPrimOp p =>
      opAlg.eval p state inputs
    for (register, retVal) in ← instr.registers.zip? retVals do
      env := env.insert register retVal
    state := state'
  return ⟨callStack.dropLast, [opAlg.novalue], state⟩

theorem Block.eval_eq_evalStep (blocks : List (Block opAlg)) (s : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (cs : List Nat) (b : Block opAlg)
    (args : List opAlg.Data) :
    Block.eval blocks s env cs b args =
      evalStep (fun s e c b a => Block.eval blocks s e c b a) blocks s env cs b args := by
  rw [Block.eval.eq_1]; rfl

/-- `partial_correctness`, phrased with `evalStep`. -/
theorem Block.eval_induct (blocks : List (Block opAlg))
    (motive : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
      List opAlg.Data → opAlg.BlockResult → Prop)
    (step : ∀ f, (∀ s e c b a r, f s e c b a = some r → motive s e c b a r) →
      ∀ s e c b a r, evalStep f blocks s e c b a = some r → motive s e c b a r) :
    ∀ s e c b a r, Block.eval blocks s e c b a = some r → motive s e c b a r :=
  Block.eval.partial_correctness blocks motive fun f hf s e c b a r h => step f hf s e c b a r h


/-! ### Stepping `evalStep` -/

@[simp] theorem zip?_nil_nil {α β : Type _} : ([] : List α).zip? ([] : List β) = some [] := rfl

section Steps
variable (f : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
      List opAlg.Data → Option opAlg.BlockResult)
    (blocks : List (Block opAlg)) (s : opAlg.State) (env : Std.HashMap String opAlg.Data)
    (cs : List Nat)

theorem evalStep_args (bargs : List String) (instrs : List opAlg.Instruction)
    (args : List opAlg.Data) :
    evalStep f blocks s env cs ⟨bargs, instrs⟩ args =
      (bargs.zip? args).bind fun ps => evalStep f blocks s (bindPairs env ps) cs ⟨[], instrs⟩ [] := by
  rcases h : bargs.zip? args with _ | ps
  · simp [evalStep, h]
  simp [evalStep, h, forIn_insert, bindPairs]

theorem evalStep_nil :
    evalStep f blocks s env cs ⟨[], []⟩ [] = some ⟨cs.dropLast, [opAlg.novalue], s⟩ := by
  simp [evalStep, List.zip?]

theorem evalStep_prim (regs : List String) (p : opAlg.PrimOp) (as : List opAlg.Arg)
    (rest : List opAlg.Instruction) :
    evalStep f blocks s env cs ⟨[], ⟨regs, .ofPrimOp p, as⟩ :: rest⟩ [] =
      ((as.mapM fun a : opAlg.Arg => a.instantiate env).bind fun ins =>
        (opAlg.eval p s ins).bind fun r =>
        (regs.zip? r.1).bind fun ps =>
          evalStep f blocks r.2 (bindPairs env ps) cs ⟨[], rest⟩ []) := by
  simp only [evalStep, zip?_nil_nil]
  simp [forIn_insert, bindPairs]
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) as with _ | ins
  · simp [hm]
  rcases he : opAlg.eval p s ins with _ | ⟨rv, s'⟩
  · simp [hm, he]
  rcases hz : regs.zip? rv with _ | ps
  · simp [hm, he, hz]
  simp [hm, he, hz, forIn_insert]

theorem evalStep_ret (regs : List String) (t : opAlg.Arg) (as : List opAlg.Arg)
    (rest : List opAlg.Instruction) :
    evalStep f blocks s env cs ⟨[], ⟨regs, .ret t, as⟩ :: rest⟩ [] =
      ((as.mapM fun a : opAlg.Arg => a.instantiate env).bind fun ins =>
        (t.instantiate env).bind fun tv =>
        (opAlg.toBlockIdx? tv).bind fun i => some ⟨cs.dropFromLast i, ins, s⟩) := by
  simp only [evalStep, zip?_nil_nil]
  simp [forIn_insert, bindPairs]
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) as with _ | ins
  · simp [hm]
  rcases ht : t.instantiate env with _ | tv
  · simp [hm, ht]
  rcases hi : opAlg.toBlockIdx? tv with _ | i
  · simp [hm, ht, hi]
  simp [hm, ht, hi]

theorem evalStep_call (regs : List String) (t : opAlg.Arg) (as : List opAlg.Arg)
    (rest : List opAlg.Instruction) :
    evalStep f blocks s env cs ⟨[], ⟨regs, .call t, as⟩ :: rest⟩ [] =
      ((as.mapM fun a : opAlg.Arg => a.instantiate env).bind fun ins =>
        (t.instantiate env).bind fun tv =>
        (opAlg.toBlockIdx? tv).bind fun j =>
        blocks[j]?.bind fun b =>
        (f s env (cs ++ [j]) b ins).bind fun r =>
          if r.callStack.length < cs.length then some r
          else (regs.zip? r.retVals).bind fun ps =>
            evalStep f blocks r.state (bindPairs env ps) cs ⟨[], rest⟩ []) := by
  simp only [evalStep, zip?_nil_nil]
  simp [forIn_insert, bindPairs]
  rcases hm : List.mapM (fun a : opAlg.Arg => a.instantiate env) as with _ | ins
  · simp [hm]
  rcases ht : t.instantiate env with _ | tv
  · simp [hm, ht]
  rcases hi : opAlg.toBlockIdx? tv with _ | j
  · simp [hm, ht, hi]
  rcases hb : blocks[j]? with _ | b
  · simp [hm, ht, hi, hb]
  rcases hr : f s env (cs ++ [j]) b ins with _ | r
  · simp [hm, ht, hi, hb, hr]
  simp only [hm, ht, hi, hb, hr, Option.bind_some]
  split
  · simp
  rcases hz : regs.zip? r.retVals with _ | ps
  · simp [hz]
  simp only [hz, Option.bind_some]

end Steps


/-! ## Well-scoped blocks are functions -/

/-- Two environments agree on the registers `D`. -/
def Agree (D : List String) (e₁ e₂ : Std.HashMap String opAlg.Data) : Prop :=
  ∀ n ∈ D, e₁[n]? = e₂[n]?

theorem mapM_agree {D : List String} {e₁ e₂ : Std.HashMap String opAlg.Data} (h : Agree D e₁ e₂) :
    ∀ {as : List opAlg.Arg}, argsDefined D as = true →
      (as.mapM fun a : opAlg.Arg => a.instantiate e₁) = (as.mapM fun a => a.instantiate e₂)
  | [], _ => rfl
  | a :: as, hd => by
    simp only [argsDefined, List.all_cons, Bool.and_eq_true] at hd
    have ih := mapM_agree h (as := as) (by simpa [argsDefined] using hd.2)
    simp only [List.mapM_cons, ih]
    cases a with
    | ofData _ => rfl
    | ofVar n =>
      have hn : n ∈ D := by simpa using hd.1
      simp [Arg.instantiate, Std.HashMap.get?_eq_getElem?, h n hn]

theorem instantiate_agree {D : List String} {e₁ e₂ : Std.HashMap String opAlg.Data}
    (h : Agree D e₁ e₂) {t : opAlg.Arg} (hd : argsDefined D [t] = true) :
    t.instantiate e₁ = t.instantiate e₂ := by
  have := mapM_agree h hd
  simp only [List.mapM_cons, List.mapM_nil] at this
  rcases h₁ : t.instantiate e₁ with _ | v₁ <;> rcases h₂ : t.instantiate e₂ with _ | v₂ <;>
    simp_all

theorem Agree.bindPairs {D : List String} {e₁ e₂ : Std.HashMap String opAlg.Data}
    (h : Agree D e₁ e₂) (ps : List (String × opAlg.Data)) :
    Agree (ps.map Prod.fst ++ D) (OpAlgebra.bindPairs e₁ ps) (OpAlgebra.bindPairs e₂ ps) := by
  induction ps generalizing D e₁ e₂ with
  | nil => simpa using h
  | cons p ps ih =>
    simp only [bindPairs_cons]
    have h' : Agree (p.1 :: D) (e₁.insert p.1 p.2) (e₂.insert p.1 p.2) := by
      intro n hn
      simp only [Std.HashMap.getElem?_insert]
      split
      · rfl
      · rename_i hne
        rcases List.mem_cons.1 hn with rfl | hn
        · simp at hne
        · exact h n hn
    intro n hn
    apply ih h' n
    simp only [List.map_cons, List.cons_append, List.mem_cons, List.mem_append] at hn ⊢
    rcases hn with hn | hn | hn
    · exact Or.inr (Or.inl hn)
    · exact Or.inl hn
    · exact Or.inr (Or.inr hn)


theorem zip?_keys {α β : Type _} {xs : List α} {ys : List β} {ps : List (α × β)}
    (h : xs.zip? ys = some ps) : ps.map Prod.fst = xs := by
  simp only [List.zip?] at h
  split at h
  · cases h; exact List.map_fst_zip (by simp_all)
  · cases h

theorem wellScoped_get {P : List (Block opAlg)} (hws : Block.WellScoped P) {i : Nat}
    {b : Block opAlg} (hb : P[i]? = some b) : instrsWellScoped i b.args b.instructions = true := by
  have hi : i < P.length := (List.getElem?_eq_some_iff.1 hb).1
  have := List.all_eq_true.1 hws i (List.mem_range.2 hi)
  simpa [hb] using this

variable (P : List (Block opAlg))

/-- What a successful run in one calling context tells us: the call returns to its
caller, and it succeeds with the same result in every calling context. -/
def Transfers : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
    List opAlg.Data → opAlg.BlockResult → Prop :=
  fun s _ cs b a r => ∀ i c, cs = c ++ [i] → P[i]? = some b →
    r.callStack = c ∧ ∀ env₂ c₂, Block.eval P s env₂ (c₂ ++ [i]) b a = some ⟨c₂, r.retVals, r.state⟩

theorem instrs_transfer (f : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
      List opAlg.Data → Option opAlg.BlockResult)
    (hf : ∀ s e c b a r, f s e c b a = some r → Transfers P s e c b a r) (i : Nat) :
    ∀ (instrs : List opAlg.Instruction) (D : List String) (s : opAlg.State)
      (envA envB : Std.HashMap String opAlg.Data) (c c₂ : List Nat) (r : opAlg.BlockResult),
      instrsWellScoped i D instrs = true → Agree D envA envB →
      evalStep f P s envA (c ++ [i]) ⟨[], instrs⟩ [] = some r →
      r.callStack = c ∧
        Block.eval P s envB (c₂ ++ [i]) ⟨[], instrs⟩ [] = some ⟨c₂, r.retVals, r.state⟩
  | [], _, s, _, envB, c, c₂, r, _, _, h => by
    rw [evalStep_nil] at h
    cases h
    refine ⟨by simp, ?_⟩
    rw [Block.eval_eq_evalStep, evalStep_nil]
    simp
  | ⟨regs, op, as⟩ :: rest, D, s, envA, envB, c, c₂, r, hws, hag, h => by
    simp only [instrsWellScoped, Bool.and_eq_true] at hws
    obtain ⟨⟨hargs, hop⟩, hrest⟩ := hws
    have hmap := mapM_agree hag hargs
    cases op with
    | ofPrimOp p =>
      rw [evalStep_prim] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ins, hm, ⟨rv, s'⟩, he, ps, hz, hr⟩ := h
      have hag' : Agree (regs ++ D) (bindPairs envA ps) (bindPairs envB ps) := by
        simpa [zip?_keys hz] using hag.bindPairs ps
      obtain ⟨h1, h2⟩ := instrs_transfer f hf i rest (regs ++ D) s' _ _ c c₂ r hrest hag' hr
      refine ⟨h1, ?_⟩
      rw [Block.eval_eq_evalStep, evalStep_prim, ← hmap, hm]
      simp only [Option.bind_some, he, hz]
      rw [← Block.eval_eq_evalStep]
      exact h2
    | call t =>
      simp only at hop
      rw [evalStep_call] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ins, hm, tv, ht, j, hj, bj, hbj, rj, hfj, hcont⟩ := h
      obtain ⟨hrj, hrj_any⟩ := hf _ _ _ _ _ _ hfj j (c ++ [i]) rfl hbj
      rw [if_neg (by simp [hrj])] at hcont
      obtain ⟨ps, hz, hr⟩ := Option.bind_eq_some_iff.1 hcont
      have hag' : Agree (regs ++ D) (bindPairs envA ps) (bindPairs envB ps) := by
        simpa [zip?_keys hz] using hag.bindPairs ps
      obtain ⟨h1, h2⟩ := instrs_transfer f hf i rest (regs ++ D) rj.state _ _ c c₂ r hrest hag' hr
      refine ⟨h1, ?_⟩
      rw [Block.eval_eq_evalStep, evalStep_call, ← hmap, hm, ← instantiate_agree hag hop, ht]
      simp only [Option.bind_some, hj, hbj]
      rw [hrj_any envB (c₂ ++ [i])]
      simp only [Option.bind_some, Nat.lt_irrefl, if_false, hz]
      rw [← Block.eval_eq_evalStep]
      exact h2
    | ret t =>
      cases t with
      | ofVar _ => simp at hop
      | ofData l =>
        simp only [beq_iff_eq] at hop
        rw [evalStep_ret] at h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨ins, hm, tv, htv, i', hi', hr⟩ := h
        simp only [Arg.instantiate, Option.some.injEq] at htv
        subst htv
        rw [hop, Option.some.injEq] at hi'
        subst hi'
        cases hr
        refine ⟨by simp, ?_⟩
        rw [Block.eval_eq_evalStep, evalStep_ret, ← hmap, hm]
        simp [Arg.instantiate, hop]

/-- **Transfer**: in a well-scoped program, a successful run of a block in one calling
context returns to its caller, and gives the same result in every calling context. -/
theorem Block.eval_transfer (hws : Block.WellScoped P) :
    ∀ s e cs b a r, Block.eval P s e cs b a = some r → Transfers P s e cs b a r :=
  Block.eval_induct P (Transfers P) fun f hf s e cs b a r h i c hcs hb => by
    subst hcs
    have hbws := wellScoped_get hws hb
    obtain ⟨bargs, instrs⟩ := b
    rw [evalStep_args] at h
    obtain ⟨ps, hz, h'⟩ := Option.bind_eq_some_iff.1 h
    have hag : ∀ envB : Std.HashMap String opAlg.Data,
        Agree bargs (bindPairs e ps) (bindPairs envB ps) := fun envB => by
      simpa [zip?_keys hz] using (show Agree [] e envB from fun _ hn => absurd hn (by simp)).bindPairs ps
    have key := fun (envB : Std.HashMap String opAlg.Data) c₂ =>
      instrs_transfer P f hf i instrs bargs s _ (bindPairs envB ps) c c₂ r hbws (hag envB) h'
    refine ⟨(key ∅ []).1, fun env₂ c₂ => ?_⟩
    rw [Block.eval_args, hz, Option.bind_some]
    exact (key _ c₂).2


/-- **A well-scoped block is a function**: called with any environment and any call
stack underneath, it gives exactly `Block.fn`, and returns to its caller. -/
theorem Block.eval_wellScoped (hws : Block.WellScoped P) {i : Nat} {b : Block opAlg}
    (hb : P[i]? = some b) (s : opAlg.State) (env : Std.HashMap String opAlg.Data)
    (cs : List Nat) (args : List opAlg.Data) :
    Block.eval P s env (cs ++ [i]) b args = (Block.fn P i args s).map fun r => ⟨cs, r.1, r.2⟩ := by
  have T := Block.eval_transfer P hws
  simp only [Block.fn, hb, Option.bind_some, Option.bind_eq_bind]
  rcases h₁ : Block.eval P s env (cs ++ [i]) b args with _ | r
  · rcases h₂ : Block.eval P s ∅ [i] b args with _ | r'
    · rfl
    obtain ⟨-, hall⟩ := T _ _ _ _ _ _ h₂ i [] rfl hb
    rw [hall env cs] at h₁
    cases h₁
  · obtain ⟨hcs, hall⟩ := T _ _ _ _ _ _ h₁ i cs rfl hb
    have h₀ := hall ∅ []
    simp only [List.nil_append] at h₀
    rcases r with ⟨rcs, rv, rs⟩
    simp only at hcs
    subst hcs
    simp [h₀]

/-- **`call` in a well-scoped program** is a function call: evaluate the arguments, run
the callee's `Block.fn`, bind its results, and continue. -/
theorem Block.eval_call_wellScoped (hws : Block.WellScoped P) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (target : opAlg.Arg) (cargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {t : opAlg.Data} {j : Nat} {b : Block opAlg}
    (ht : target.instantiate env = some t) (hj : opAlg.toBlockIdx? t = some j)
    (hb : P[j]? = some b) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], ⟨regs, .call target, cargs⟩ :: rest⟩ noargs =
      ((cargs.mapM (fun a : opAlg.Arg => a.instantiate env)).bind fun inputs =>
        (Block.fn P j inputs state).bind fun r =>
        (regs.zip? r.1).bind fun pairs =>
          Block.eval P r.2 (bindPairs env pairs) callStack ⟨[], rest⟩ []) := by
  rw [Block.eval_call _ _ _ _ _ _ _ _ hno]
  simp only [ht, hj, hb, Block.eval_wellScoped P hws hb, Option.bind_some]
  rcases (cargs.mapM fun a : opAlg.Arg => a.instantiate env) with _ | inputs
  · rfl
  simp only [Option.bind_some]
  rcases Block.fn P j inputs state with _ | ⟨v, s'⟩
  · rfl
  simp


/-- `simp`-usable form of `Block.eval_call_wellScoped`: the target is computed in the
right-hand side, so the only side condition is `WellScoped`. -/
theorem Block.eval_call_ws (hws : Block.WellScoped P) (state : opAlg.State)
    (env : Std.HashMap String opAlg.Data) (callStack : List Nat)
    (regs : List String) (target : opAlg.Arg) (cargs : List opAlg.Arg)
    (rest : List opAlg.Instruction) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], ⟨regs, .call target, cargs⟩ :: rest⟩ noargs =
      ((cargs.mapM (fun a : opAlg.Arg => a.instantiate env)).bind fun inputs =>
        (target.instantiate env).bind fun t =>
        (opAlg.toBlockIdx? t).bind fun j =>
        (Block.fn P j inputs state).bind fun r =>
        (regs.zip? r.1).bind fun pairs =>
          Block.eval P r.2 (bindPairs env pairs) callStack ⟨[], rest⟩ []) := by
  rcases ht : target.instantiate env with _ | t
  · rw [Block.eval_call _ _ _ _ _ _ _ _ hno, ht]
    rcases (cargs.mapM fun a : opAlg.Arg => a.instantiate env) <;> rfl
  rcases hj : opAlg.toBlockIdx? t with _ | j
  · rw [Block.eval_call _ _ _ _ _ _ _ _ hno, ht]
    simp [hj]
  rcases hb : P[j]? with _ | b
  · rw [Block.eval_call _ _ _ _ _ _ _ _ hno, ht]
    simp [hj, hb, Block.fn]
  rw [Block.eval_call_wellScoped P hws _ _ _ _ _ _ _ ht hj hb hno]
  simp [ht, hj]

/-- End of a block: fall through, returning `[novalue]`. -/
@[block_eval] theorem Block.eval_nil (state : opAlg.State) (env : Std.HashMap String opAlg.Data)
    (callStack : List Nat) {noargs : List opAlg.Data} (hno : noargs = []) :
    Block.eval P state env callStack ⟨[], []⟩ noargs =
      some ⟨callStack.dropLast, [opAlg.novalue], state⟩ := by
  subst hno
  rw [Block.eval_eq_evalStep, evalStep_nil]


/-- Unfold a top-level call of a block: bind its arguments and run its instructions. -/
theorem Block.fn_unfold (i : Nat) (args : List opAlg.Data) (s : opAlg.State) :
    Block.fn P i args s =
      P[i]?.bind fun b => (b.args.zip? args).bind fun ps =>
        (Block.eval P s (bindPairs ∅ ps) [i] ⟨[], b.instructions⟩ []).bind fun r =>
          if r.callStack = [] then some (r.retVals, r.state) else none := by
  simp only [Block.fn, Option.bind_eq_bind]
  rcases P[i]? with _ | ⟨bargs, instrs⟩
  · rfl
  simp only [Option.bind_some]
  rw [Block.eval_args]
  rcases bargs.zip? args <;> rfl

@[simp, block_eval] theorem dropFromLast_singleton (i : Nat) : [i].dropFromLast i = [] := by
  simpa using dropFromLast_append_self [] i


/-- `Block.fn_unfold` for a literal block index only, so `simp` unfolds a call once its
target is known, and not before. -/
theorem Block.fn_unfold_lit (i : Nat) (args : List opAlg.Data) (s : opAlg.State) :
    Block.fn P (OfNat.ofNat i) args s =
      P[(OfNat.ofNat i : Nat)]?.bind fun b => (b.args.zip? args).bind fun ps =>
        (Block.eval P s (bindPairs ∅ ps) [OfNat.ofNat i] ⟨[], b.instructions⟩ []).bind fun r =>
          if r.callStack = [] then some (r.retVals, r.state) else none :=
  Block.fn_unfold P _ args s


/-- Bind a block's arguments (only for blocks that have some, so `simp` terminates). -/
@[block_eval] theorem Block.eval_bind_args (s : opAlg.State) (e : Std.HashMap String opAlg.Data)
    (cs : List Nat) (a : String) (as : List String) (instrs : List opAlg.Instruction)
    (vs : List opAlg.Data) :
    Block.eval P s e cs ⟨a :: as, instrs⟩ vs =
      ((a :: as).zip? vs).bind fun ps => Block.eval P s (bindPairs e ps) cs ⟨[], instrs⟩ [] :=
  Block.eval_args P s e cs _ instrs vs

end OpAlgebra
