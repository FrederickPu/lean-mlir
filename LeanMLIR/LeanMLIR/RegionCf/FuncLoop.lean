/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCf.Mono
import LeanMLIR.RegionCf.Simp
import LeanMLIR.RegionCf.Arith

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

namespace RegionCfFunctor.FuncLoop

abbrev N : Ty Arith.Ty := .base .nat
abbrev F : Ty Arith.Ty := .fn

/-- The loop's body, on `(i, acc, f)`: `acc + f(i)`, then `i - 1`. -/
def loopAst : Region 0 := [mlir_region| {
  ^bb0(%i : !nat, %acc : !nat, %f : !fn):
    %flag, %i', %acc', %f' = "cf.ite"(%i, %i, %acc, %f) ({
      ^bb0(%i : !nat, %acc : !nat, %f : !fn):
        %s = "cf.call"(%f, %i) : (!fn, !nat) -> (!nat)
        %acc1 = "arith.add"(%acc, %s) : (!nat, !nat) -> (!nat)
        %one = "arith.cst"() {value = 1} : () -> (!nat)
        %i1 = "arith.sub"(%i, %one) : (!nat, !nat) -> (!nat)
        "return"(%one, %i1, %acc1, %f) : (!nat, !nat, !nat, !fn) -> ()
    }, {
      ^bb0(%i : !nat, %acc : !nat, %f : !fn):
        %zero = "arith.cst"() {value = 0} : () -> (!nat)
        "return"(%zero, %i, %acc, %f) : (!nat, !nat, !nat, !fn) -> ()
    }) : (!nat, !nat, !nat, !fn) -> (!nat, !nat, !nat, !fn)
    "return"(%flag, %i', %acc', %f') : (!nat, !nat, !nat, !fn) -> ()
}]

/-- `sq(n) = n * n` -/
def sqAst : Region 0 := [mlir_region| {
  ^bb0(%sq : !fn, %sumsq : !fn, %n : !nat):
    %r = "arith.mul"(%n, %n) : (!nat, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-- `sumsq(n)`: the loop, from `(n, 0, sq)`. -/
def sumsqAst : Region 0 := [mlir_region| {
  ^bb0(%sq : !fn, %sumsq : !fn, %n : !nat):
    %c0 = "arith.cst"() {value = 0} : () -> (!nat)
    %i, %acc, %f = "cf.while"(%n, %c0, %sq) ($(loopAst)) :
      (!nat, !nat, !fn) -> (!nat, !nat, !fn)
    "return"(%acc) : (!nat) -> ()
}]

abbrev loopBody := [cf_region| $(loopAst)]
abbrev sqBody := [cf_region| $(sqAst)]
abbrev sumsqBody := [cf_region| $(sumsqAst)]

/-- `funcs { sq; sumsq } in sumsq(n)` -/
def prog := [cf| {
  ^bb0(%n : !nat):
    %r = "cf.funcs"(%n) ({
      ^bb0(%sq : !fn, %sumsq : !fn, %n : !nat):
        %r = "cf.call"(%sumsq, %n) : (!fn, !nat) -> (!nat)
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
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (show Nat from r.head)

#guard (List.range 8).all fun n => Sumsq' n == some (sumsq n)

/-! ## The loop, for any function computing squares -/

/-- A value: a number. -/
abbrev V := Val Arith.Ty
/-- A function value. -/
abbrev FV := List V → Option (List V)

/-- A function value that computes squares. -/
def IsSq (fv : FV) : Prop := ∀ i : Nat, fv [⟨.nat, i⟩] = some [⟨.nat, i * i⟩]

abbrev step (st : HVector toType [N, N, F]) : Option (Bool × HVector toType [N, N, F]) :=
  (loopBody.denote (Valuation.ofHVector (rev st))).map fun r => (Base.isTrue (d := Arith) r.head, r.tail)

theorem step_zero (acc : Nat) (fv : FV) :
    step ((0 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some (false, (0 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) :=
  rfl

theorem step_succ (i acc : Nat) (fv : FV) (hf : IsSq fv) :
    step ((i + 1 : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some (true, (i : Nat) ::ₕ (acc + (i + 1) * (i + 1) : Nat) ::ₕ fv ::ₕ .nil) := by
  unfold step loopBody
  cf_reduce
  rw [hf]
  rfl

/-- The loop's invariant: the function is `fv`, and `acc + sumsq i` is the final value. -/
def Inv (fv : FV) (target : Nat) : HVector toType [N, N, F] → Prop
  | .cons (i : Nat) (.cons (acc : Nat) (.cons (f : FV) .nil)) =>
    f = fv ∧ acc + sumsq i = target

/-- The loop's measure: `i`. -/
def measure : HVector toType [N, N, F] → Nat
  | .cons (i : Nat) _ => i

/-- **The loop adds `sumsq i`**, calling `fv` once per step. -/
theorem loop (fv : FV) (hf : IsSq fv) (i acc : Nat) :
    whileLoop step ((i : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) =
      some ((0 : Nat) ::ₕ (acc + sumsq i : Nat) ::ₕ fv ::ₕ .nil) := by
  obtain ⟨y, hy, hq⟩ := whileLoop_inv step (Inv fv (acc + sumsq i))
    (· = ((0 : Nat) ::ₕ (acc + sumsq i : Nat) ::ₕ fv ::ₕ .nil)) measure
    (by
      rintro (_ | ⟨(i' : Nat), _ | ⟨(a : Nat), _ | ⟨(f : FV), ⟨⟩⟩⟩⟩) hP
      obtain ⟨rfl, hP⟩ := hP
      cases i' with
      | zero =>
        refine ⟨false, _, step_zero a f, fun _ => ?_, by simp⟩
        simp only [sumsq, Nat.add_zero] at hP; rw [← hP]
      | succ i' =>
        refine ⟨true, _, step_succ i' a f hf, by simp, fun _ => ⟨⟨rfl, ?_⟩, ?_⟩⟩
        · simp only [sumsq] at hP; show a + (i' + 1) * (i' + 1) + sumsq i' = _; omega
        · simp [measure])
    ((i : Nat) ::ₕ (acc : Nat) ::ₕ fv ::ₕ .nil) ⟨rfl, rfl⟩
  rw [hy, hq]

/-! ## The functions -/

/-- The signatures of `sq` and `sumsq`: a number to a number. -/
abbrev sigs : List (List Arith.Ty × List Arith.Ty) := [([.nat], [.nat]), ([.nat], [.nat])]

/-- The bodies, as the `funcs` op's regions. -/
abbrev bodyRegs : HVector (fun t : Ctxt (Ty Arith.Ty) × List (Ty Arith.Ty) =>
    _root_.Com (RegionCf Arith) t.1 .impure t.2) (bodySig sigs sigs) :=
  .cons sqBody (.cons sumsqBody .nil)

theorem hFb : RegsMono (HVector.denote (d := RegionCf Arith) bodyRegs) :=
  HVector.denote_mono (d := Arith) bodyRegs

/-- The functions of the program. -/
noncomputable abbrev T : FnTable V :=
  funcsFix fun Tb => bodies sigs Tb sigs (HVector.denote (d := RegionCf Arith) bodyRegs)

theorem T_sq : IsSq (T 0) := fun i =>
  (funcsFix_apply _ _ hFb 0 [⟨.nat, i⟩]).trans rfl

theorem T_sumsq (n : Nat) : T 1 [⟨.nat, n⟩] = some [⟨.nat, sumsq n⟩] := by
  refine (funcsFix_apply _ _ hFb 1 _).trans ?_
  show Option.map (toVals (ts := [Arith.Ty.nat])) (sumsqBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) = _
  unfold sumsqBody
  cf_reduce
  rw [loop (T 0) T_sq n 0]
  cf_reduce
  simp

/-- **The program computes `sumsq`.** -/
theorem Sumsq'_eq (n : Nat) : Sumsq' n = some (sumsq n) := by
  unfold Sumsq' prog
  cf_reduce
  -- `T` unfolded, so that its `funcsFix` head matches the reduced program
  have h := T_sumsq n
  unfold T at h
  rw [h]
  rfl

end RegionCfFunctor.FuncLoop
