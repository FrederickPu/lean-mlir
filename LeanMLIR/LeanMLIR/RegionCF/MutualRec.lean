/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.Mono
import LeanMLIR.RegionCF.Simp
import LeanMLIR.RegionCF.Syntax

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

namespace RegionCF.MutualRec

open MLIR.AST (Region)

abbrev N := Ty.nat
abbrev F := Ty.fn 1 1

/-- `f(n) = if n == 0 then 0 else 3 * g(n - 1) + n * n + 7` -/
def fAst : Region 0 := [mlir_region| {
  ^bb0(%f : !fn_1_1, %g : !fn_1_1, %n : !nat):
    %z = "cf.eqz"(%n) : (!nat) -> (!nat)
    %r = "cf.ite"(%z, %g, %n) ({
      ^bb0(%g : !fn_1_1, %n : !nat):
        %c = "cf.cst"() {value = 0} : () -> (!nat)
        "return"(%c) : (!nat) -> ()
    }, {
      ^bb0(%g : !fn_1_1, %n : !nat):
        %one = "cf.cst"() {value = 1} : () -> (!nat)
        %m = "cf.sub"(%n, %one) : (!nat, !nat) -> (!nat)
        %a = "cf.call"(%g, %m) : (!fn_1_1, !nat) -> (!nat)
        %three = "cf.cst"() {value = 3} : () -> (!nat)
        %b = "cf.mul"(%three, %a) : (!nat, !nat) -> (!nat)
        %sq = "cf.mul"(%n, %n) : (!nat, !nat) -> (!nat)
        %c = "cf.add"(%b, %sq) : (!nat, !nat) -> (!nat)
        %seven = "cf.cst"() {value = 7} : () -> (!nat)
        %res = "cf.add"(%c, %seven) : (!nat, !nat) -> (!nat)
        "return"(%res) : (!nat) -> ()
    }) : (!nat, !fn_1_1, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

/-- `g(n) = if n == 0 then 1 else 2 * f(n - 1) + n + 5` -/
def gAst : Region 0 := [mlir_region| {
  ^bb0(%f : !fn_1_1, %g : !fn_1_1, %n : !nat):
    %z = "cf.eqz"(%n) : (!nat) -> (!nat)
    %r = "cf.ite"(%z, %f, %n) ({
      ^bb0(%f : !fn_1_1, %n : !nat):
        %c = "cf.cst"() {value = 1} : () -> (!nat)
        "return"(%c) : (!nat) -> ()
    }, {
      ^bb0(%f : !fn_1_1, %n : !nat):
        %one = "cf.cst"() {value = 1} : () -> (!nat)
        %m = "cf.sub"(%n, %one) : (!nat, !nat) -> (!nat)
        %a = "cf.call"(%f, %m) : (!fn_1_1, !nat) -> (!nat)
        %two = "cf.cst"() {value = 2} : () -> (!nat)
        %b = "cf.mul"(%two, %a) : (!nat, !nat) -> (!nat)
        %c = "cf.add"(%b, %n) : (!nat, !nat) -> (!nat)
        %five = "cf.cst"() {value = 5} : () -> (!nat)
        %res = "cf.add"(%c, %five) : (!nat, !nat) -> (!nat)
        "return"(%res) : (!nat) -> ()
    }) : (!nat, !fn_1_1, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

def fBody := [cf_region| $(fAst)]
def gBody := [cf_region| $(gAst)]

/-- `funcs { f; g } in f(n)` -/
def prog := [cf| {
  ^bb0(%n : !nat):
    %r = "cf.funcs"(%n) ({
      ^bb0(%f : !fn_1_1, %g : !fn_1_1, %n : !nat):
        %r = "cf.call"(%f, %n) : (!fn_1_1, !nat) -> (!nat)
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
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (r.head : Nat)

#guard (List.range 8).all fun n => F' n == some (f n)

/-! ## The proof

Each body, run on its arguments (`cf_reduce` evaluates the program), is its equation; the
table of the group is monotone, so it is the fixpoint of its bodies (`funcsFix_unfold`); by
induction, it is `f` and `g`. -/

open Lean.Order

theorem fBody_denote (fv gv : List Nat → Option (List Nat)) (n : Nat) :
    fBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) =
      if n = 0 then some ((0 : Nat) ::ₕ .nil) else
        (gv [n - 1]).bind fun r => (ofNats 1 r).bind fun a =>
          some ((3 * (a.head : Nat) + n * n + 7 : Nat) ::ₕ .nil) := by
  unfold fBody
  cases n with
  | zero => rfl
  | succ n =>
    cf_reduce
    simp only [Option.bind_assoc, Nat.add_sub_cancel]
    cf_reduce
    simp only [Option.bind_map, Option.map_bind, Option.bind_assoc, Function.comp_def]
    congr 1; funext r
    rcases ofNats 1 r with _ | (_ | ⟨x, xs⟩)
    · rfl
    · cases xs; rfl

theorem gBody_denote (fv gv : List Nat → Option (List Nat)) (n : Nat) :
    gBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ gv ::ₕ fv ::ₕ .nil)) =
      if n = 0 then some ((1 : Nat) ::ₕ .nil) else
        (fv [n - 1]).bind fun r => (ofNats 1 r).bind fun a =>
          some ((2 * (a.head : Nat) + n + 5 : Nat) ::ₕ .nil) := by
  unfold gBody
  cases n with
  | zero => rfl
  | succ n =>
    cf_reduce
    simp only [Option.bind_assoc, Nat.add_sub_cancel]
    cf_reduce
    simp only [Option.bind_map, Option.map_bind, Option.bind_assoc, Function.comp_def]
    congr 1; funext r
    rcases ofNats 1 r with _ | (_ | ⟨x, xs⟩)
    · rfl
    · cases xs; rfl

/-- The bodies of `f` and `g`, as a table transformer. -/
abbrev Fb : FnTable → FnTable := fun T =>
  bodies [(1, 1), (1, 1)] T [(1, 1), (1, 1)] (Com.denote fBody ::ₕ Com.denote gBody ::ₕ .nil)

/-- The functions of the program. -/
noncomputable abbrev T : FnTable := funcsFix Fb

/-- The bodies, as the `funcs` op's regions. -/
def bodyRegs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2)
    ([(1, 1), (1, 1)].map fun (n, m) => (⟨(fnTys [(1, 1), (1, 1)] ++ nats n).reverse⟩, nats m)) :=
  .cons fBody (.cons gBody .nil)

/-- The bodies are monotone: true of every program (`Com.denote_mono`). -/
theorem hFb : RegsMono (HVector.denote (d := CF) bodyRegs) := HVector.denote_mono bodyRegs

/-- Each function's equation: `funcsFix_apply`, for any group, with monotonicity from the
general theorem (`HVector.denote_mono`); the rest is computation. -/
theorem T_f (n : Nat) :
    T 0 [n] = Option.map (toNats (n := 1))
      (fBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 0 [n]).trans rfl
theorem T_g (n : Nat) :
    T 1 [n] = Option.map (toNats (n := 1))
      (gBody.denote (Valuation.ofHVector ((n : Nat) ::ₕ T 1 ::ₕ T 0 ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 1 [n]).trans rfl

theorem table : (n : Nat) → T 0 [n] = some [f n] ∧ T 1 [n] = some [g n]
  | 0 => by rw [T_f, T_g, fBody_denote, gBody_denote]; simp [f, g]; exact ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨ihf, ihg⟩ := table n
    rw [T_f, T_g, fBody_denote, gBody_denote]
    simp [ihf, ihg, f, g, ofNats]; exact ⟨rfl, rfl⟩

/-- **The program computes `f`.** -/
theorem F'_eq (n : Nat) : F' n = some (f n) := by
  unfold F' prog
  cf_reduce
  have h : funcsFix Fb 0 [n] = some [f n] := (table n).1
  erw [h]
  rfl

end RegionCF.MutualRec
