/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCf.Mono
import LeanMLIR.RegionCf.Simp
import LeanMLIR.RegionCf.Arith

/-!
# Mutually recursive functions, as a region op

```
funcs {
  f(n) = if n == 0 then 0 else 3 * g(n - 1) + n * n + 7
  g(n) = if n == 0 then 1 else 2 * f(n - 1) + n + 5
} in f(n)
```
-/

open Ctxt (Var Valuation)
open TyDenote (toType)

namespace RegionCfFunctor.MutualRec

open MLIR.AST (Region)

abbrev N : Ty Arith.Ty := .base .nat
abbrev F : Ty Arith.Ty := .fn

/-- `f(n) = if n == 0 then 0 else 3 * g(n - 1) + n * n + 7` -/
def fAst : Region 0 := [mlir_region| {
  ^bb0(%f : !fn, %g : !fn, %n : !nat):
    %z = "arith.eqz"(%n) : (!nat) -> (!nat)
    %r = "cf.ite"(%z, %g, %n) ({
      ^bb0(%g : !fn, %n : !nat):
        %c = "arith.cst"() {value = 0} : () -> (!nat)
        "return"(%c) : (!nat) -> ()
    }, {
      ^bb0(%g : !fn, %n : !nat):
        %one = "arith.cst"() {value = 1} : () -> (!nat)
        %m = "arith.sub"(%n, %one) : (!nat, !nat) -> (!nat)
        %a = "cf.call"(%g, %m) : (!fn, !nat) -> (!nat)
        %three = "arith.cst"() {value = 3} : () -> (!nat)
        %b = "arith.mul"(%three, %a) : (!nat, !nat) -> (!nat)
        %sq = "arith.mul"(%n, %n) : (!nat, !nat) -> (!nat)
        %c = "arith.add"(%b, %sq) : (!nat, !nat) -> (!nat)
        %seven = "arith.cst"() {value = 7} : () -> (!nat)
        %res = "arith.add"(%c, %seven) : (!nat, !nat) -> (!nat)
        "return"(%res) : (!nat) -> ()
    }) : (!nat, !fn, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-- `g(n) = if n == 0 then 1 else 2 * f(n - 1) + n + 5` -/
def gAst : Region 0 := [mlir_region| {
  ^bb0(%f : !fn, %g : !fn, %n : !nat):
    %z = "arith.eqz"(%n) : (!nat) -> (!nat)
    %r = "cf.ite"(%z, %f, %n) ({
      ^bb0(%f : !fn, %n : !nat):
        %c = "arith.cst"() {value = 1} : () -> (!nat)
        "return"(%c) : (!nat) -> ()
    }, {
      ^bb0(%f : !fn, %n : !nat):
        %one = "arith.cst"() {value = 1} : () -> (!nat)
        %m = "arith.sub"(%n, %one) : (!nat, !nat) -> (!nat)
        %a = "cf.call"(%f, %m) : (!fn, !nat) -> (!nat)
        %two = "arith.cst"() {value = 2} : () -> (!nat)
        %b = "arith.mul"(%two, %a) : (!nat, !nat) -> (!nat)
        %c = "arith.add"(%b, %n) : (!nat, !nat) -> (!nat)
        %five = "arith.cst"() {value = 5} : () -> (!nat)
        %res = "arith.add"(%c, %five) : (!nat, !nat) -> (!nat)
        "return"(%res) : (!nat) -> ()
    }) : (!nat, !fn, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

def fBody := [cf_region| $(fAst)]
def gBody := [cf_region| $(gAst)]

/-- `funcs { f; g } in f(n)` -/
def prog := [cf| {
  ^bb0(%n : !nat):
    %r = "cf.funcs"(%n) ({
      ^bb0(%f : !fn, %g : !fn, %n : !nat):
        %r = "cf.call"(%f, %n) : (!fn, !nat) -> (!nat)
        "return"(%r) : (!nat) -> ()
    }, $(fAst), $(gAst)) : (!nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-! ## The specification -/

mutual
def f : Nat → Nat
  | 0 => 0
  | n + 1 => 3 * g n + (n + 1) * (n + 1) + 7
def g : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * f n + (n + 1) + 5
end

/-- `f`, computed by the program. -/
def F' (n : Nat) : Option Nat :=
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (show Nat from r.head)

#guard (List.range 8).all fun n => F' n == some (f n)

/-! ## The proof

Each body, run on its arguments (`cf_reduce` evaluates the program), is its equation; the
table of the group is monotone, so it is the fixpoint of its bodies (`funcsFix_unfold`); by
induction, it is `f` and `g`. -/

open Lean.Order

/-- A value: a number. -/
abbrev V := Val Arith.Ty
/-- A function value. -/
abbrev FV := List V → Option (List V)

theorem fBody_zero (fv gv : FV) :
    fBody.denote (Valuation.ofHVector ((0 : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) = some ((0 : Nat) ::ₕ .nil) :=
  rfl

theorem fBody_succ (fv gv : FV) (n : Nat) :
    fBody.denote (Valuation.ofHVector ((n + 1 : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) =
      (gv [⟨.nat, n⟩]).bind fun r => (ofVals [.nat] r).bind fun a =>
        some ((3 * (show Nat from a.head) + (n + 1) * (n + 1) + 7 : Nat) ::ₕ .nil) := by
  unfold fBody
  cf_simp
  congr 1; funext r
  rcases ofVals [Arith.Ty.nat] r with _ | (_ | ⟨x, xs⟩)
  · rfl
  · cases xs; rfl

theorem gBody_zero (fv gv : FV) :
    gBody.denote (Valuation.ofHVector ((0 : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) = some ((1 : Nat) ::ₕ .nil) :=
  rfl

theorem gBody_succ (fv gv : FV) (n : Nat) :
    gBody.denote (Valuation.ofHVector ((n + 1 : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) =
      (fv [⟨.nat, n⟩]).bind fun r => (ofVals [.nat] r).bind fun a =>
        some ((2 * (show Nat from a.head) + (n + 1) + 5 : Nat) ::ₕ .nil) := by
  unfold gBody
  cf_simp
  congr 1; funext r
  rcases ofVals [Arith.Ty.nat] r with _ | (_ | ⟨x, xs⟩)
  · rfl
  · cases xs; rfl

/-- The signatures of `f` and `g`: a number to a number. -/
abbrev sigs : List (List Arith.Ty × List Arith.Ty) := [([.nat], [.nat]), ([.nat], [.nat])]

/-- The bodies of `f` and `g`, as a table transformer. -/
abbrev Fb : FnTable V → FnTable V := fun Tb =>
  bodies sigs Tb sigs (Com.denote fBody ::ₕ Com.denote gBody ::ₕ .nil)

/-- The functions of the program. -/
noncomputable abbrev T : FnTable V := funcsFix Fb

/-- The bodies, as the `funcs` op's regions. -/
def bodyRegs : HVector (fun t : Ctxt (Ty Arith.Ty) × List (Ty Arith.Ty) =>
    _root_.Com (RegionCf Arith) t.1 .impure t.2) (bodySig sigs sigs) :=
  .cons fBody (.cons gBody .nil)

/-- The bodies are monotone: true of every program (`Com.denote_mono`). -/
theorem hFb : RegsMono (HVector.denote (d := RegionCf Arith) bodyRegs) := HVector.denote_mono (d := Arith) bodyRegs

/-- Each function's equation: `funcsFix_apply`, for any group, with monotonicity from the
general theorem (`HVector.denote_mono`); the rest is computation. -/
theorem T_f (n : Nat) :
    T 0 [⟨.nat, n⟩] = Option.map (toVals (ts := [Arith.Ty.nat]))
      (fBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 0 _).trans rfl
theorem T_g (n : Nat) :
    T 1 [⟨.nat, n⟩] = Option.map (toVals (ts := [Arith.Ty.nat]))
      (gBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 1 _).trans rfl

theorem table : (n : Nat) →
    T 0 [⟨.nat, n⟩] = some [⟨.nat, f n⟩] ∧ T 1 [⟨.nat, n⟩] = some [⟨.nat, g n⟩]
  | 0 => by rw [T_f, T_g, fBody_zero, gBody_zero]; exact ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨ihf, ihg⟩ := table n
    rw [T_f, T_g, fBody_succ, gBody_succ, ihf, ihg]
    exact ⟨rfl, rfl⟩

/-- **The program computes `f`.** -/
theorem F'_eq (n : Nat) : F' n = some (f n) := by
  unfold F' prog
  cf_reduce
  have h : funcsFix Fb 0 [⟨.nat, n⟩] = some [⟨.nat, f n⟩] := (table n).1
  erw [h]
  rfl

end RegionCfFunctor.MutualRec
