/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Std

/-!
# Loops and mutual recursion, as Lean functions

The semantics of the control-flow region ops (`RegionCF.Dialect`):

* `whileLoop body x`: run `body` while it asks to continue. Defined by `partial_fixpoint`,
  so it is a Lean function (in `Option`: a loop that never stops has no value), with the
  unfolding equation `whileLoop_unfold`.
* `funcsFix F`: the table of a group of mutually recursive functions, the least fixpoint of
  `F`, where `F T i` is function `i`'s body calling the functions of `T`. When `F` is
  monotone (as every program's is), `funcsFix_unfold` gives each function's equation, as
  Lean's equation lemmas do for a `mutual` definition.
-/

open Lean.Order

namespace RegionCF

/-- `while`: run `body` on the state; it returns a flag (`0`: stop) and the new state. -/
def whileLoop {α : Type} (body : α → Option (Nat × α)) (x : α) : Option α := do
  let (c, x') ← body x
  if c = 0 then pure x' else whileLoop body x'
partial_fixpoint

theorem whileLoop_unfold {α : Type} (body : α → Option (Nat × α)) (x : α) :
    whileLoop body x = (body x).bind fun r => if r.1 = 0 then some r.2 else whileLoop body r.2 := by
  rw [whileLoop]; rfl

/-- **A loop with an invariant and a decreasing measure stops**, in a state satisfying `Q`.

At every state satisfying the invariant `P`, the body returns a flag and a new state:
on a break (flag `0`) the new state satisfies `Q`; on a continue, it satisfies `P` and has a
smaller measure `μ`. -/
theorem whileLoop_inv {α : Type} (body : α → Option (Nat × α)) (P Q : α → Prop) (μ : α → Nat)
    (h : ∀ x, P x → ∃ c y, body x = some (c, y) ∧ (c = 0 → Q y) ∧ (c ≠ 0 → P y ∧ μ y < μ x))
    (x : α) (hx : P x) : ∃ y, whileLoop body x = some y ∧ Q y := by
  obtain ⟨c, y, hb, h0, h1⟩ := h x hx
  rw [whileLoop_unfold, hb]
  by_cases hc : c = 0
  · exact ⟨y, by simp [hc], h0 hc⟩
  · obtain ⟨hy, hlt⟩ := h1 hc
    obtain ⟨z, hz, hq⟩ := whileLoop_inv body P Q μ h y hy
    exact ⟨z, by simp [hc, hz], hq⟩
termination_by μ x
decreasing_by exact hlt

/-- **A loop that never breaks has no value.** At every state satisfying the invariant `P`,
the body continues (a nonzero flag) to a state satisfying `P`. -/
theorem whileLoop_diverges {α : Type} (body : α → Option (Nat × α)) (P : α → Prop)
    (h : ∀ x, P x → ∃ c y, body x = some (c, y) ∧ c ≠ 0 ∧ P y) :
    ∀ x, P x → whileLoop body x = none := by
  refine whileLoop.fixpoint_induct body (fun w => ∀ x, P x → w x = none) ?_ ?_
  · apply admissible_pi; intro x
    apply admissible_pi; intro _
    exact admissible_apply (fun _ o => o = none) x (admissible_flatOrder _ rfl)
  · intro w hw x hx
    obtain ⟨c, y, hb, hc, hy⟩ := h x hx
    dsimp only
    rw [hb]
    show (if c = 0 then some y else w y) = none
    rw [if_neg hc]
    exact hw y hy

/-- A table of functions on lists of numbers (by index). -/
abbrev FnTable := Nat → List Nat → Option (List Nat)

/-- Run a table's bodies by unbounded recursion (the compiled implementation). -/
partial def funcsFixImpl (F : FnTable → FnTable) : FnTable :=
  fun i xs => F (funcsFixImpl F) i xs

open Classical in
/-- **Mutually recursive functions**: the least fixpoint of `F` (no functions if `F` is not
monotone). -/
@[implemented_by funcsFixImpl]
noncomputable def funcsFix (F : FnTable → FnTable) : FnTable :=
  if h : monotone F then fix F h else fun _ _ => none

/-- **The equations of mutually recursive functions**: each is its body, calling the others. -/
theorem funcsFix_unfold {F : FnTable → FnTable} (h : monotone F) : funcsFix F = F (funcsFix F) := by
  simp only [funcsFix, dif_pos h]
  exact fix_eq h

end RegionCF
