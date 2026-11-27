/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std

/-!
# Loops and mutual recursion, as Lean functions

The semantics of the control-flow region ops (`LeanMLIR.RegionCf.Dialect`):

* `whileLoop body x`: run `body` while it asks to continue. Defined by `partial_fixpoint`,
  so it is a Lean function (in `Option`: a loop that never stops has no value), with the
  unfolding equation `whileLoop_unfold`.
* `funcsFix F`: the table of a group of mutually recursive functions, the least fixpoint of
  `F`, where `F T i` is function `i`'s body calling the functions of `T`. When `F` is
  monotone (as every program's is), `funcsFix_unfold` gives each function's equation, as
  Lean's equation lemmas do for a `mutual` definition.
-/

open Lean.Order

namespace RegionCfFunctor

/-- `while`: run `body` on the state; it returns a flag (`false`: stop) and the new state. -/
def whileLoop {α : Type} (body : α → Option (Bool × α)) (x : α) : Option α := do
  let (c, x') ← body x
  if c then whileLoop body x' else pure x'
partial_fixpoint

theorem whileLoop_unfold {α : Type} (body : α → Option (Bool × α)) (x : α) :
    whileLoop body x = (body x).bind fun r => if r.1 then whileLoop body r.2 else some r.2 := by
  rw [whileLoop]; rfl

/-- **A loop with an invariant and a decreasing measure stops**, in a state satisfying `Q`.

At every state satisfying the invariant `P`, the body returns a flag and a new state:
on a break (flag `false`) the new state satisfies `Q`; on a continue, it satisfies `P` and
has a smaller measure `μ`. -/
theorem whileLoop_inv {α : Type} (body : α → Option (Bool × α)) (P Q : α → Prop) (μ : α → Nat)
    (h : ∀ x, P x → ∃ c y, body x = some (c, y) ∧ (c = false → Q y) ∧
      (c = true → P y ∧ μ y < μ x))
    (x : α) (hx : P x) : ∃ y, whileLoop body x = some y ∧ Q y := by
  obtain ⟨c, y, hb, h0, h1⟩ := h x hx
  rw [whileLoop_unfold, hb]
  cases c with
  | false => exact ⟨y, rfl, h0 rfl⟩
  | true =>
    obtain ⟨hy, hlt⟩ := h1 rfl
    obtain ⟨z, hz, hq⟩ := whileLoop_inv body P Q μ h y hy
    exact ⟨z, hz, hq⟩
termination_by μ x
decreasing_by exact hlt

/-- **A loop that never breaks has no value.** At every state satisfying the invariant `P`,
the body continues (flag `true`) to a state satisfying `P`. -/
theorem whileLoop_diverges {α : Type} (body : α → Option (Bool × α)) (P : α → Prop)
    (h : ∀ x, P x → ∃ y, body x = some (true, y) ∧ P y) :
    ∀ x, P x → whileLoop body x = none := by
  refine whileLoop.fixpoint_induct body (fun w => ∀ x, P x → w x = none) ?_ ?_
  · apply admissible_pi; intro x
    apply admissible_pi; intro _
    exact admissible_apply (fun _ o => o = none) x (admissible_flatOrder _ rfl)
  · intro w hw x hx
    obtain ⟨y, hb, hy⟩ := h x hx
    dsimp only
    rw [hb]
    exact hw y hy

/-- A table of functions on lists of values `V` (by index). -/
abbrev FnTable (V : Type) := Nat → List V → Option (List V)

/-- Run a table's bodies by unbounded recursion (the compiled implementation). -/
partial def funcsFixImpl {V : Type} (F : FnTable V → FnTable V) : FnTable V :=
  fun i xs => F (funcsFixImpl F) i xs

open Classical in
/-- **Mutually recursive functions**: the least fixpoint of `F` (no functions if `F` is not
monotone). -/
@[implemented_by funcsFixImpl]
noncomputable def funcsFix {V : Type} (F : FnTable V → FnTable V) : FnTable V :=
  if h : monotone F then fix F h else fun _ _ => none

/-- **The equations of mutually recursive functions**: each is its body, calling the others. -/
theorem funcsFix_unfold {V : Type} {F : FnTable V → FnTable V} (h : monotone F) :
    funcsFix F = F (funcsFix F) := by
  simp only [funcsFix, dif_pos h]
  exact fix_eq h

end RegionCfFunctor
