/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.Mono
import LeanMLIR.RegionCF.Simp
import LeanMLIR.RegionCF.Syntax

/-!
# Loops and functions together

```
funcs {
  sq(n)    = n * n
  sumsq(n) = acc := 0; for i in n down to 1: acc := acc + sq(i); return acc
} in sumsq(n)
```

A loop inside a function body, calling a function inside the loop. Regions see only their
block arguments, so the loop gets `sq` through its state, `(i, acc, sq)`.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open MLIR.AST (Region)

namespace RegionCF.FuncLoop

abbrev N := Ty.nat
abbrev F := Ty.fn 1 1

/-- The loop's body, on `(i, acc, f)`: `acc + f(i)`, then `i - 1`. -/
def loopAst : Region 0 := [mlir_region| {
  ^bb0(%i : !nat, %acc : !nat, %f : !fn_1_1):
    %flag, %i', %acc', %f' = "cf.ite"(%i, %i, %acc, %f) ({
      ^bb0(%i : !nat, %acc : !nat, %f : !fn_1_1):
        %s = "cf.call"(%f, %i) : (!fn_1_1, !nat) -> (!nat)
        %acc1 = "cf.add"(%acc, %s) : (!nat, !nat) -> (!nat)
        %one = "cf.cst"() {value = 1} : () -> (!nat)
        %i1 = "cf.sub"(%i, %one) : (!nat, !nat) -> (!nat)
        "return"(%one, %i1, %acc1, %f) : (!nat, !nat, !nat, !fn_1_1) -> ()
    }, {
      ^bb0(%i : !nat, %acc : !nat, %f : !fn_1_1):
        %zero = "cf.cst"() {value = 0} : () -> (!nat)
        "return"(%zero, %i, %acc, %f) : (!nat, !nat, !nat, !fn_1_1) -> ()
    }) : (!nat, !nat, !nat, !fn_1_1) -> (!nat, !nat, !nat, !fn_1_1)
    "return"(%flag, %i', %acc', %f') : (!nat, !nat, !nat, !fn_1_1) -> ()
}]

/-- `sq(n) = n * n` -/
def sqAst : Region 0 := [mlir_region| {
  ^bb0(%sq : !fn_1_1, %sumsq : !fn_1_1, %n : !nat):
    %r = "cf.mul"(%n, %n) : (!nat, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-- `sumsq(n)`: the loop, from `(n, 0, sq)`. -/
def sumsqAst : Region 0 := [mlir_region| {
  ^bb0(%sq : !fn_1_1, %sumsq : !fn_1_1, %n : !nat):
    %c0 = "cf.cst"() {value = 0} : () -> (!nat)
    %i, %acc, %f = "cf.while"(%n, %c0, %sq) ($(loopAst)) :
      (!nat, !nat, !fn_1_1) -> (!nat, !nat, !fn_1_1)
    "return"(%acc) : (!nat) -> ()
}]

def loopBody := [cf_region| $(loopAst)]
def sqBody := [cf_region| $(sqAst)]
def sumsqBody := [cf_region| $(sumsqAst)]

/-- `funcs { sq; sumsq } in sumsq(n)` -/
def prog := [cf| {
  ^bb0(%n : !nat):
    %r = "cf.funcs"(%n) ({
      ^bb0(%sq : !fn_1_1, %sumsq : !fn_1_1, %n : !nat):
        %r = "cf.call"(%sumsq, %n) : (!fn_1_1, !nat) -> (!nat)
        "return"(%r) : (!nat) -> ()
    }, $(sqAst), $(sumsqAst)) : (!nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-! ## The specification -/

/-- `1² + … + n²` -/
def sumsq : Nat → Nat
  | 0 => 0
  | n + 1 => (n + 1) * (n + 1) + sumsq n

def Sumsq' (n : Nat) : Option Nat :=
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (r.head : Nat)

#guard (List.range 8).all fun n => Sumsq' n == some (sumsq n)

/-! ## The loop, for any function computing squares -/

/-- A function value that computes squares. -/
def IsSq (fv : List Nat → Option (List Nat)) : Prop := ∀ i, fv [i] = some [i * i]

abbrev step (st : HVector toType [N, N, F]) : Option (Nat × HVector toType [N, N, F]) :=
  (loopBody.denote (Valuation.ofHVector (rev st))).map fun r => (r.head, r.tail)

theorem step_zero (acc : Nat) (fv : List Nat → Option (List Nat)) :
    step ((0 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some (0, (0 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) :=
  rfl

theorem step_succ (i acc : Nat) (fv : List Nat → Option (List Nat)) (hf : IsSq fv) :
    step ((i + 1 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some (1, (i : Nat) ::ₕ (acc + (i + 1) * (i + 1) : Nat) ::ₕ fv ::ₕ .nil) := by
  unfold step loopBody
  cf_reduce
  rw [hf]
  rfl

/-- The loop's invariant: the function is `fv`, and `acc + sumsq i` is the final value. -/
def Inv (fv : List Nat → Option (List Nat)) (target : Nat) : HVector toType [N, N, F] → Prop
  | .cons (i : Nat) (.cons (acc : Nat) (.cons (f : List Nat → Option (List Nat)) .nil)) =>
    f = fv ∧ acc + sumsq i = target

/-- The loop's measure: `i`. -/
def measure : HVector toType [N, N, F] → Nat
  | .cons (i : Nat) _ => i

/-- **The loop adds `sumsq i`**, calling `fv` once per step. -/
theorem loop (fv : List Nat → Option (List Nat)) (hf : IsSq fv) (i acc : Nat) :
    whileLoop step ((i : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some ((0 : Nat) ::ₕ (acc + sumsq i : Nat) ::ₕ fv ::ₕ .nil) := by
  obtain ⟨y, hy, hq⟩ := whileLoop_inv step (Inv fv (acc + sumsq i))
    (· = ((0 : Nat) ::ₕ (acc + sumsq i : Nat) ::ₕ fv ::ₕ .nil)) measure
    (by
      rintro (_ | ⟨(i' : Nat), _ | ⟨(a : Nat), _ | ⟨(f : List Nat → Option (List Nat)), ⟨⟩⟩⟩⟩) hP
      obtain ⟨rfl, hP⟩ := hP
      cases i' with
      | zero =>
        refine ⟨0, _, step_zero a f, fun _ => ?_, by simp⟩
        simp only [sumsq, Nat.add_zero] at hP; rw [← hP]
      | succ i' =>
        refine ⟨1, _, step_succ i' a f hf, by simp, fun _ => ⟨⟨rfl, ?_⟩, ?_⟩⟩
        · simp only [sumsq] at hP; show a + (i' + 1) * (i' + 1) + sumsq i' = _; omega
        · simp [measure])
    ((i : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) ⟨rfl, rfl⟩
  rw [hy, hq]

/-! ## The functions -/

/-- The bodies, as the `funcs` op's regions. -/
def bodyRegs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2)
    ([(1, 1), (1, 1)].map fun (n, m) => (⟨(fnTys [(1, 1), (1, 1)] ++ nats n).reverse⟩, nats m)) :=
  .cons sqBody (.cons sumsqBody .nil)

theorem hFb : RegsMono (HVector.denote (d := CF) bodyRegs) := HVector.denote_mono bodyRegs

/-- The functions of the program. -/
noncomputable abbrev T : FnTable :=
  funcsFix fun T =>
    bodies [(1, 1), (1, 1)] T [(1, 1), (1, 1)] (Com.denote sqBody ::ₕ Com.denote sumsqBody ::ₕ .nil)

theorem T_sq : IsSq (T 0) := fun i =>
  (funcsFix_apply _ _ hFb 0 [i]).trans rfl

theorem T_sumsq (n : Nat) : T 1 [n] = some [sumsq n] := by
  refine (funcsFix_apply _ _ hFb 1 [n]).trans ?_
  show Option.map (toNats (n := 1)) (sumsqBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) = _
  unfold sumsqBody
  cf_reduce
  erw [loop (T 0) T_sq n 0]
  cf_reduce
  simp

/-- **The program computes `sumsq`.** -/
theorem Sumsq'_eq (n : Nat) : Sumsq' n = some (sumsq n) := by
  unfold Sumsq' prog
  cf_reduce
  have h : funcsFix _ 1 [n] = some [sumsq n] := T_sumsq n
  erw [h]
  rfl

end RegionCF.FuncLoop
