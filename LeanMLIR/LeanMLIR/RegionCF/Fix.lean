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
