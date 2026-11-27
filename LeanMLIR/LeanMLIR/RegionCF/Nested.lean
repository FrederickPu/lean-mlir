/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.Mono
import LeanMLIR.RegionCF.Simp
import LeanMLIR.RegionCF.Syntax

/-!
# Nested loops

```
acc := 0
for i in n down to 1:        -- outer loop, state (i, m, acc)
  for j in m down to 1:      -- inner loop, state (j, acc)
    acc := acc + 1
return acc
```

computes `n * m`. Each loop is proved with the generic `whileLoop_inv` (an invariant and a
decreasing measure); the outer body's step uses the inner loop's lemma.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open MLIR.AST (Region)

namespace RegionCF.Nested

abbrev N := Ty.nat

/-- The inner loop's body, on `(j, acc)`: add `1`, `j` times. -/
def innerAst : Region 0 := [mlir_region| {
  ^bb0(%j : !nat, %acc : !nat):
    %f, %j', %acc' = "cf.ite"(%j, %j, %acc) ({
      ^bb0(%j : !nat, %acc : !nat):
        %one = "cf.cst"() {value = 1} : () -> (!nat)
        %j1 = "cf.sub"(%j, %one) : (!nat, !nat) -> (!nat)
        %acc1 = "cf.add"(%acc, %one) : (!nat, !nat) -> (!nat)
        "return"(%one, %j1, %acc1) : (!nat, !nat, !nat) -> ()
    }, {
      ^bb0(%j : !nat, %acc : !nat):
        %zero = "cf.cst"() {value = 0} : () -> (!nat)
        "return"(%zero, %j, %acc) : (!nat, !nat, !nat) -> ()
    }) : (!nat, !nat, !nat) -> (!nat, !nat, !nat)
    "return"(%f, %j', %acc') : (!nat, !nat, !nat) -> ()
}]

/-- The outer loop's body, on `(i, m, acc)`: run the inner loop (`acc + m`), `i` times. -/
def outerAst : Region 0 := [mlir_region| {
  ^bb0(%i : !nat, %m : !nat, %acc : !nat):
    %f, %i', %m', %acc' = "cf.ite"(%i, %i, %m, %acc) ({
      ^bb0(%i : !nat, %m : !nat, %acc : !nat):
        %j, %acc2 = "cf.while"(%m, %acc) ($(innerAst)) : (!nat, !nat) -> (!nat, !nat)
        %one = "cf.cst"() {value = 1} : () -> (!nat)
        %i1 = "cf.sub"(%i, %one) : (!nat, !nat) -> (!nat)
        "return"(%one, %i1, %m, %acc2) : (!nat, !nat, !nat, !nat) -> ()
    }, {
      ^bb0(%i : !nat, %m : !nat, %acc : !nat):
        %zero = "cf.cst"() {value = 0} : () -> (!nat)
        "return"(%zero, %i, %m, %acc) : (!nat, !nat, !nat, !nat) -> ()
    }) : (!nat, !nat, !nat, !nat) -> (!nat, !nat, !nat, !nat)
    "return"(%f, %i', %m', %acc') : (!nat, !nat, !nat, !nat) -> ()
}]

def inner := [cf_region| $(innerAst)]
def outer := [cf_region| $(outerAst)]

/-- `acc := 0; while outer; return acc` -/
def prog := [cf| {
  ^bb0(%n : !nat, %m : !nat):
    %c0 = "cf.cst"() {value = 0} : () -> (!nat)
    %i, %m', %r = "cf.while"(%n, %m, %c0) ($(outerAst)) : (!nat, !nat, !nat) -> (!nat, !nat, !nat)
    "return"(%r) : (!nat) -> ()
}]

/-- `n * m`, computed by the program (its arguments `(%n, %m)`, as a context read backwards). -/
def Mul' (n m : Nat) : Option Nat :=
  (prog.denote (Valuation.ofHVector (rev ((n : Nat) ::ₕ (m : Nat) ::ₕ .nil)))).map
    fun r => (r.head : Nat)

#guard (List.range 5).all fun n => (List.range 5).all fun m => Mul' n m == some (n * m)

/-! ## The inner loop -/

abbrev innerStep (st : HVector toType [N, N]) : Option (Nat × HVector toType [N, N]) :=
  (inner.denote (Valuation.ofHVector (rev st))).map fun r => (r.head, r.tail)

theorem innerStep_zero (acc : Nat) :
    innerStep ((0 : Nat) ::ₕ (acc : Nat) ::ₕ .nil) = some (0, (0 : Nat) ::ₕ (acc : Nat) ::ₕ .nil) :=
  rfl

theorem innerStep_succ (j acc : Nat) :
    innerStep ((j + 1 : Nat) ::ₕ (acc : Nat) ::ₕ .nil) =
      some (1, (j : Nat) ::ₕ (acc + 1 : Nat) ::ₕ .nil) :=
  rfl

/-- The inner loop's invariant: `acc + j` is the final value. -/
def innerInv (target : Nat) : HVector toType [N, N] → Prop
  | .cons (j : Nat) (.cons (acc : Nat) .nil) => acc + j = target

/-- The inner loop's measure: `j`. -/
def innerMeasure : HVector toType [N, N] → Nat
  | .cons (j : Nat) _ => j

/-- **The inner loop adds `j`.** -/
theorem inner_loop (j acc : Nat) :
    whileLoop innerStep ((j : Nat) ::ₕ (acc : Nat) ::ₕ .nil) =
      some ((0 : Nat) ::ₕ (acc + j : Nat) ::ₕ .nil) := by
  obtain ⟨y, hy, hq⟩ := whileLoop_inv innerStep (innerInv (acc + j))
    (· = ((0 : Nat) ::ₕ (acc + j : Nat) ::ₕ .nil)) innerMeasure
    (by
      rintro (_ | ⟨(j' : Nat), _ | ⟨(a : Nat), ⟨⟩⟩⟩) hP
      simp only [innerInv] at hP
      cases j' with
      | zero => exact ⟨0, _, innerStep_zero a, fun _ => by rw [← hP]; rfl, by simp⟩
      | succ j' =>
        refine ⟨1, _, innerStep_succ j' a, by simp, fun _ => ⟨?_, ?_⟩⟩
        · simp only [innerInv]; omega
        · simp [innerMeasure])
    ((j : Nat) ::ₕ (acc : Nat) ::ₕ .nil) rfl
  rw [hy, hq]

/-! ## The outer loop -/

abbrev outerStep (st : HVector toType [N, N, N]) : Option (Nat × HVector toType [N, N, N]) :=
  (outer.denote (Valuation.ofHVector (rev st))).map fun r => (r.head, r.tail)

theorem outerStep_zero (m acc : Nat) :
    outerStep ((0 : Nat) ::ₕ (m : Nat) ::ₕ (acc : Nat) ::ₕ .nil) =
      some (0, (0 : Nat) ::ₕ (m : Nat) ::ₕ (acc : Nat) ::ₕ .nil) :=
  rfl

theorem outerStep_succ (i m acc : Nat) :
    outerStep ((i + 1 : Nat) ::ₕ (m : Nat) ::ₕ (acc : Nat) ::ₕ .nil) =
      some (1, (i : Nat) ::ₕ (m : Nat) ::ₕ (acc + m : Nat) ::ₕ .nil) := by
  unfold outerStep outer
  cf_reduce
  -- the inner loop, run as far as `cf_reduce` goes: still `innerStep`, up to unfolding
  erw [inner_loop m acc]
  rfl

/-- The outer loop's invariant: `m` is unchanged, and `acc + i * m` is the final value. -/
def outerInv (m target : Nat) : HVector toType [N, N, N] → Prop
  | .cons (i : Nat) (.cons (m' : Nat) (.cons (acc : Nat) .nil)) => m' = m ∧ acc + i * m = target

/-- The outer loop's measure: `i`. -/
def outerMeasure : HVector toType [N, N, N] → Nat
  | .cons (i : Nat) _ => i

/-- **The outer loop adds `i * m`.** -/
theorem outer_loop (i m acc : Nat) :
    whileLoop outerStep ((i : Nat) ::ₕ (m : Nat) ::ₕ (acc : Nat) ::ₕ .nil) =
      some ((0 : Nat) ::ₕ (m : Nat) ::ₕ (acc + i * m : Nat) ::ₕ .nil) := by
  obtain ⟨y, hy, hq⟩ := whileLoop_inv outerStep (outerInv m (acc + i * m))
    (· = ((0 : Nat) ::ₕ (m : Nat) ::ₕ (acc + i * m : Nat) ::ₕ .nil)) outerMeasure
    (by
      rintro (_ | ⟨(i' : Nat), _ | ⟨(m' : Nat), _ | ⟨(a : Nat), ⟨⟩⟩⟩⟩) hP
      obtain ⟨rfl, hP⟩ := hP
      cases i' with
      | zero =>
        refine ⟨0, _, outerStep_zero m' a, fun _ => ?_, by simp⟩
        simp only [Nat.zero_mul, Nat.add_zero] at hP; rw [← hP]
      | succ i' =>
        refine ⟨1, _, outerStep_succ i' m' a, by simp, fun _ => ⟨⟨rfl, ?_⟩, ?_⟩⟩
        · rw [Nat.succ_mul] at hP; show a + m' + i' * m' = _; omega
        · simp [outerMeasure])
    ((i : Nat) ::ₕ (m : Nat) ::ₕ (acc : Nat) ::ₕ .nil) ⟨rfl, rfl⟩
  rw [hy, hq]

/-- **The program computes `n * m`.** -/
theorem Mul'_eq (n m : Nat) : Mul' n m = some (n * m) := by
  unfold Mul' prog
  cf_reduce
  erw [outer_loop n m 0]
  cf_reduce
  simp

end RegionCF.Nested
