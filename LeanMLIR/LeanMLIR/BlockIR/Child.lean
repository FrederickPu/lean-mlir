/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.WellScoped

/-!
# Children: blocks whose returns stay inside their caller

**Policy.** Block `B` is a *child* of block `A` if all return paths from `B`, when it
is called from `A`, go through `A` first.

**Formalization (`Block.Child`).** "Called from `A`" means `B` runs with `A`'s frame on
top of the call stack: `cs ++ [A, B]`, for any `cs` underneath. A run of `B` ends with
some call stack; it "goes through `A` first" when it does not unwind past `A`'s frame
other than by popping that frame itself, i.e. the final stack is at least as long as
`cs`. (A `ret` to `A`, e.g. an early return from the function `A`, pops `A`'s frame and
lands exactly on `cs`: that goes through `A`.) This is a property of the semantics
`Block.eval`, quantified over every environment, state, argument list and `cs`.

**Decision procedure (`Block.childDec`).** Compute, for every block, the set of labels
its runs may unwind to beyond its own frame (`escapes`), by a fixpoint over the call
graph: a block's own `ret`s to other labels, plus the escapes of anything it may call,
minus itself (a callee unwinding to `B` just makes `B` return). A call through a register
may reach any block. Then check the result is closed under these rules (`closed`), and
that `B` escapes only to `A`.

**Correctness (`Block.child_of_childDec`).** If `childDec P A B = true` then
`Block.Child P A B`. The procedure is sound but not complete: it can answer `false` for
a child (e.g. one that could unwind further only along a path that never executes),
since deciding `Block.Child` exactly is undecidable in general.
-/

namespace OpAlgebra
variable {opAlg : OpAlgebra}

/-! ## The policy, as a property of `Block.eval` -/

/-- **`B` is a child of `A`**: every run of `B`, called from `A` (with `A`'s frame on top
of any call stack `cs`), ends without unwinding past `A`'s frame except by popping it. -/
def Block.Child (P : List (Block opAlg)) (A B : Nat) : Prop :=
  ∀ b, P[B]? = some b → ∀ (s : opAlg.State) (env : Std.HashMap String opAlg.Data)
    (cs : List Nat) (args : List opAlg.Data) (r : opAlg.BlockResult),
    Block.eval P s env (cs ++ [A, B]) b args = some r → cs.length ≤ r.callStack.length

/-! ## The decision procedure -/

/-- Which blocks a `call` with target `t` may reach: a constant label reaches one block;
a register may hold any label. -/
def callTargets (P : List (Block opAlg)) : opAlg.Arg → List Nat
  | .ofData d => match opAlg.toBlockIdx? d with
    | some j => [j]
    | none => []
  | .ofVar _ => List.range P.length

/-- `L` is allowed as an escape of block `B` under the assignment `E`. -/
def escapesOK (E : Nat → List Nat) (B L : Nat) : Bool := L == B || (E B).contains L

/-- One instruction of block `B` respects the escape assignment `E`. -/
def instrClosed (P : List (Block opAlg)) (E : Nat → List Nat) (B : Nat)
    (i : opAlg.Instruction) : Bool :=
  match i.op with
  | .ofPrimOp _ => true
  | .ret (.ofData d) => match opAlg.toBlockIdx? d with
    | some L => escapesOK E B L
    | none => true
  | .ret (.ofVar _) => false
  | .call t => (callTargets P t).all fun j => (E j).all (escapesOK E B)

/-- `E` is closed: every block's `ret`s and callees' escapes are covered. -/
def closed (P : List (Block opAlg)) (E : Nat → List Nat) : Bool :=
  (List.range P.length).all fun B =>
    match P[B]? with
    | some b => b.instructions.all (instrClosed P E B)
    | none => true

/-- The labels block `B` may unwind to, one round of the fixpoint. -/
def escapesStep (P : List (Block opAlg)) (E : Nat → List Nat) (B : Nat) : List Nat :=
  match P[B]? with
  | none => []
  | some b =>
    let own := b.instructions.flatMap fun i => match i.op with
      | .ret (.ofData d) => (opAlg.toBlockIdx? d).toList
      | .call t => (callTargets P t).flatMap E
      | _ => []
    (E B ++ own).filter (· != B) |>.eraseDups

/-- Rounds of the fixpoint, as a table (one entry per block), stopping once stable. -/
def escapesIter (P : List (Block opAlg)) : Nat → List (List Nat) → List (List Nat)
  | 0, E => E
  | k + 1, E =>
    let E' := (List.range P.length).map (escapesStep P fun j => E.getD j [])
    if E' == E then E else escapesIter P k E'

/-- The escapes, after enough rounds for any program of this size to stabilize. -/
def escapes (P : List (Block opAlg)) : Nat → List Nat :=
  let E := escapesIter P (P.length * P.length + 1) ((List.range P.length).map fun _ => [])
  fun B => E.getD B []

/-- **Decide** `Block.Child P A B` (soundly): the computed escapes are closed, and `B`
escapes only to `A`. -/
def Block.childDec (P : List (Block opAlg)) (A B : Nat) : Bool :=
  closed P (escapes P) && (escapes P B).all (· == A)

/-! ## Facts about unwinding -/

theorem findLastIdx?_lt {l : List Nat} {L i : Nat} (h : l.findLastIdx? (· == L) = some i) :
    i < l.length := by
  simp only [List.findLastIdx?, Option.map_eq_some_iff] at h
  obtain ⟨k, hk, rfl⟩ := h
  have := (List.findIdx?_eq_some_iff_getElem.1 hk).1
  simp only [List.length_reverse] at this
  omega

theorem findLastIdx?_concat_ne {l : List Nat} {x L : Nat} (h : L ≠ x) :
    (l ++ [x]).findLastIdx? (· == L) = l.findLastIdx? (· == L) := by
  have hx : (x == L) = false := by simp [Ne.symm h]
  unfold List.findLastIdx?
  rw [List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.findIdx?_cons, hx, Bool.false_eq_true, ↓reduceIte, Option.map_map, List.length_append,
    List.length_singleton]
  rcases hk : l.reverse.findIdx? (· == L) with _ | k
  · rfl
  · have := (List.findIdx?_eq_some_iff_getElem.1 hk).1
    simp only [List.length_reverse] at this
    simp only [Option.map_some, Function.comp_apply, Option.some.injEq]
    omega

/-- Unwinding a stack with `x` on top to a label `L ≠ x` either unwinds the rest, or (if
`L` is not on the stack) leaves it unchanged. -/
theorem dropFromLast_concat_ne {l : List Nat} {x L : Nat} (h : L ≠ x) :
    (l ++ [x]).dropFromLast L = l.dropFromLast L ∨ (l ++ [x]).dropFromLast L = l ++ [x] := by
  simp only [List.dropFromLast, findLastIdx?_concat_ne h]
  rcases hf : l.findLastIdx? (· == L) with _ | i
  · exact Or.inr rfl
  · exact Or.inl (List.take_append_of_le_length (Nat.le_of_lt (findLastIdx?_lt hf)))

theorem length_dropFromLast_le (l : List Nat) (L : Nat) : (l.dropFromLast L).length ≤ l.length := by
  simp only [List.dropFromLast]
  split <;> simp <;> omega

/-! ## Soundness -/

/-- Where a run of block `B`, started with stack `st ++ [B]`, may end: back on `st`, with
the stack unchanged, or unwound to an allowed escape. -/
def Lands (st : List Nat) (E : List Nat) (B : Nat) (r : opAlg.BlockResult) : Prop :=
  r.callStack = st ∨ r.callStack = st ++ [B] ∨ ∃ L ∈ E, r.callStack = st.dropFromLast L

theorem instrs_lands (P : List (Block opAlg)) (E : Nat → List Nat) (hE : closed P E = true)
    (f : opAlg.State → Std.HashMap String opAlg.Data → List Nat → Block opAlg →
      List opAlg.Data → Option opAlg.BlockResult)
    (hf : ∀ s e c b a r, f s e c b a = some r →
      ∀ C st, c = st ++ [C] → P[C]? = some b → Lands st (E C) C r)
    (B : Nat) :
    ∀ (instrs : List opAlg.Instruction) (s : opAlg.State)
      (env : Std.HashMap String opAlg.Data) (st : List Nat) (r : opAlg.BlockResult),
      instrs.all (instrClosed P E B) = true →
      evalStep f P s env (st ++ [B]) ⟨[], instrs⟩ [] = some r → Lands st (E B) B r
  | [], s, env, st, r, _, h => by
    rw [evalStep_nil] at h
    cases h
    exact Or.inl (by simp)
  | ⟨regs, op, as⟩ :: rest, s, env, st, r, hc, h => by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨hi, hrest⟩ := hc
    cases op with
    | ofPrimOp p =>
      rw [evalStep_prim] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ins, -, ⟨rv, s'⟩, -, ps, -, hr⟩ := h
      exact instrs_lands P E hE f hf B rest s' _ st r hrest hr
    | ret t =>
      rw [evalStep_ret] at h
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨ins, -, tv, htv, L, hL, rfl⟩ := h
      cases t with
      | ofVar _ => simp [instrClosed] at hi
      | ofData d =>
        simp only [Arg.instantiate, Option.some.injEq] at htv
        subst htv
        simp only [instrClosed, hL, escapesOK, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem]
          at hi
        show Lands st (E B) B ⟨(st ++ [B]).dropFromLast L, ins, s⟩
        rcases hi with rfl | hmem
        · exact Or.inl (dropFromLast_append_self st L)
        · by_cases hLB : L = B
          · subst hLB; exact Or.inl (dropFromLast_append_self st L)
          · rcases dropFromLast_concat_ne (l := st) hLB with h' | h'
            · exact Or.inr (Or.inr ⟨L, hmem, h'⟩)
            · exact Or.inr (Or.inl h')
    | call t =>
      rw [evalStep_call] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨ins, -, tv, htv, j, hj, bj, hbj, rj, hfj, hcont⟩ := h
      have hjt : j ∈ callTargets P t := by
        cases t with
        | ofData d =>
          simp only [Arg.instantiate, Option.some.injEq] at htv
          subst htv
          simp [callTargets, hj]
        | ofVar _ =>
          simp only [callTargets, List.mem_range]
          exact (List.getElem?_eq_some_iff.1 hbj).1
      have hcl : ∀ L ∈ E j, escapesOK E B L = true := by
        simp only [instrClosed, List.all_eq_true] at hi
        exact hi j hjt
      have hland := hf _ _ _ _ _ _ hfj j (st ++ [B]) rfl hbj
      split at hcont
      · rename_i hlt
        cases hcont
        rcases hland with h' | h' | ⟨L, hL, h'⟩
        · simp [h'] at hlt
        · simp [h'] at hlt
        · have hok := hcl L hL
          simp only [escapesOK, Bool.or_eq_true, beq_iff_eq, List.contains_iff_mem] at hok
          by_cases hLB : L = B
          · subst hLB
            exact Or.inl (h'.trans (dropFromLast_append_self st L))
          · rcases hok with hok | hok
            · exact absurd hok hLB
            rcases dropFromLast_concat_ne (l := st) hLB with h'' | h''
            · exact Or.inr (Or.inr ⟨L, hok, h'.trans h''⟩)
            · rw [h', h''] at hlt; simp at hlt
      · obtain ⟨ps, -, hr⟩ := Option.bind_eq_some_iff.1 hcont
        exact instrs_lands P E hE f hf B rest _ _ st r hrest hr

/-- Every run of a block lands as `E` allows, when `E` is closed. -/
theorem Block.eval_lands (P : List (Block opAlg)) (E : Nat → List Nat) (hE : closed P E = true) :
    ∀ s e c b a r, Block.eval P s e c b a = some r →
      ∀ C st, c = st ++ [C] → P[C]? = some b → Lands st (E C) C r :=
  Block.eval_induct P _ fun f hf s e c b a r h C st hc hb => by
    subst hc
    have hC : C < P.length := (List.getElem?_eq_some_iff.1 hb).1
    have hbc : b.instructions.all (instrClosed P E C) = true := by
      have := List.all_eq_true.1 hE C (List.mem_range.2 hC)
      simpa [hb] using this
    obtain ⟨bargs, instrs⟩ := b
    rw [evalStep_args] at h
    obtain ⟨ps, -, h'⟩ := Option.bind_eq_some_iff.1 h
    exact instrs_lands P E hE f hf C instrs s _ st r hbc h'

/-- **Correctness of the decision procedure**: if `childDec` says `B` is a child of `A`,
then it is, in the sense of `Block.Child`. -/
theorem Block.child_of_childDec (P : List (Block opAlg)) (A B : Nat)
    (h : Block.childDec P A B = true) : Block.Child P A B := by
  simp only [Block.childDec, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  obtain ⟨hE, hA⟩ := h
  intro b hb s env cs args r hr
  have hland := Block.eval_lands P (escapes P) hE s env (cs ++ [A, B]) b args r hr B (cs ++ [A])
    (by simp) hb
  rcases hland with h' | h' | ⟨L, hL, h'⟩
  · simp [h']
  · simp [h']
  · rw [hA L hL] at h'
    rw [h', dropFromLast_append_self]
    exact Nat.le_refl _

end OpAlgebra
