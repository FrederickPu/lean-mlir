/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework
import LeanMLIR.RegionCF.Fix

/-!
# A control-flow dialect, all region ops

Structured control flow inside LeanMLIR's SSA, with no other IR:

* `ite ts rs`: if-then-else, one region per branch;
* `while ts`: a loop; its body returns a flag (`0`: stop, the `break`) and the new state;
* `funcs sigs ts rs`: a group of mutually recursive functions `f₀ … fₖ`, `fᵢ` taking `nᵢ`
  and returning `mᵢ` numbers. Its regions: first the code using them, then one body per
  function. Every region sees all the functions as values (`fn n m`);
* `call n m f xs`: apply a function value.

The dialect's monad is `Option`: a loop or a recursion that does not stop has no value.
Values are numbers and functions (`⟦fn n m⟧ = List Nat → Option (List Nat)`).
-/

open Ctxt (Var Valuation)
open TyDenote (toType)

namespace RegionCF

inductive Ty
  | nat
  | fn (n m : Nat)
  deriving DecidableEq, Repr

instance : TyDenote Ty where
  toType
    | .nat => Nat
    | .fn _ _ => List Nat → Option (List Nat)

/-- The types of a group of functions. -/
def fnTys (sigs : List (Nat × Nat)) : List Ty := sigs.map fun (n, m) => .fn n m

/-- `n` numbers. -/
abbrev nats (n : Nat) : List Ty := List.replicate n .nat

inductive Op
  | cst (k : Nat)
  | add | sub | mul
  /-- `1` if the argument is `0`, else `0`. -/
  | eqz
  | ite (ts rs : List Ty)
  | while (ts : List Ty)
  | funcs (sigs : List (Nat × Nat)) (ts rs : List Ty)
  | call (n m : Nat)
  deriving Repr

abbrev CF : Dialect where
  Op := Op
  Ty := Ty
  m := Option

instance : DialectSignature CF where
  signature
    | .cst _ => ⟨[], [], [.nat], .pure⟩
    | .eqz => ⟨[.nat], [], [.nat], .pure⟩
    | .ite ts rs => ⟨.nat :: ts, [(⟨ts⟩, rs), (⟨ts⟩, rs)], rs, .impure⟩
    | .while ts => ⟨ts, [(⟨ts⟩, .nat :: ts)], ts, .impure⟩
    | .funcs sigs ts rs =>
      ⟨ts, (⟨fnTys sigs ++ ts⟩, rs) :: sigs.map (fun (n, m) => (⟨fnTys sigs ++ nats n⟩, nats m)),
        rs, .impure⟩
    | .call n m => ⟨.fn n m :: nats n, [], nats m, .impure⟩
    | _ => ⟨[.nat, .nat], [], [.nat], .pure⟩


/-! ## The effect of each op -/

@[simp] theorem effectKind_cst (k : Nat) : DialectSignature.effectKind (d := CF) (.cst k) = .pure := rfl
@[simp] theorem effectKind_add : DialectSignature.effectKind (d := CF) .add = .pure := rfl
@[simp] theorem effectKind_sub : DialectSignature.effectKind (d := CF) .sub = .pure := rfl
@[simp] theorem effectKind_mul : DialectSignature.effectKind (d := CF) .mul = .pure := rfl
@[simp] theorem effectKind_eqz : DialectSignature.effectKind (d := CF) .eqz = .pure := rfl
@[simp] theorem effectKind_ite (ts rs) : DialectSignature.effectKind (d := CF) (.ite ts rs) = .impure := rfl
@[simp] theorem effectKind_while (ts) : DialectSignature.effectKind (d := CF) (.while ts) = .impure := rfl
@[simp] theorem effectKind_funcs (sigs ts rs) :
    DialectSignature.effectKind (d := CF) (.funcs sigs ts rs) = .impure := rfl
@[simp] theorem effectKind_call (n m) : DialectSignature.effectKind (d := CF) (.call n m) = .impure := rfl
/-! ## Numbers in and out of functions -/

/-- `n` numbers as a list. -/
def toNats : {n : Nat} → HVector toType (nats n) → List Nat
  | 0, .nil => []
  | _ + 1, .cons (x : Nat) xs => x :: toNats xs

/-- A list of `n` numbers. -/
def ofNats : (n : Nat) → List Nat → Option (HVector toType (nats n))
  | 0, [] => some .nil
  | n + 1, x :: xs => (ofNats n xs).map (.cons (x : Nat))
  | _, _ => none

/-- The function values of a table, for a group of signatures (function `i` is `T i`). -/
def fnVals (T : FnTable) : (sigs : List (Nat × Nat)) → (i : Nat := 0) → HVector toType (fnTys sigs)
  | [], _ => .nil
  | _ :: sigs, i => .cons (T i) (fnVals T sigs (i + 1))

/-- A region, as `denote` receives it. -/
abbrev RegFn (t : Ctxt Ty × List Ty) := t.1.Valuation → Option (HVector toType t.2)

/-- The bodies of a group, as a table transformer: function `i` runs region `i` on the
functions of `T` and its arguments. -/
def bodies (sigs₀ : List (Nat × Nat)) (T : FnTable) : (sigs : List (Nat × Nat)) →
    HVector RegFn (sigs.map fun (n, m) => (⟨fnTys sigs₀ ++ nats n⟩, nats m)) → FnTable
  | [], .nil => fun _ _ => none
  | (n, _) :: sigs, .cons r rs => fun i xs =>
    if i = 0 then
      (ofNats n xs).bind fun ys =>
        (r (Valuation.ofHVector (fnVals T sigs₀ ++ ys))).map toNats
    else bodies sigs₀ T sigs rs (i - 1) xs

instance : DialectDenote CF where
  denote
    | .cst k, _, _ => (.cons (k : Nat) .nil : HVector toType [Ty.nat])
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a + b) .nil : HVector toType [Ty.nat])
    | .sub, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a - b) .nil : HVector toType [Ty.nat])
    | .mul, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a * b) .nil : HVector toType [Ty.nat])
    | .eqz, .cons (a : Nat) .nil, _ =>
      (.cons (if a = 0 then 1 else 0 : Nat) .nil : HVector toType [Ty.nat])
    | .ite _ _, .cons (c : Nat) xs, .cons thn (.cons els .nil) =>
      if c ≠ 0 then thn (Valuation.ofHVector xs) else els (Valuation.ofHVector xs)
    | .while _, xs, .cons body .nil =>
      whileLoop (fun st => (body (Valuation.ofHVector st)).map fun r => (r.head, r.tail)) xs
    | .funcs sigs _ _, xs, .cons main rs =>
      main (Valuation.ofHVector (fnVals (funcsFix fun T => bodies sigs T sigs rs) sigs ++ xs))
    | .call _ m, .cons (f : List Nat → Option (List Nat)) xs, _ => (f (toNats xs)).bind (ofNats m)

/-! ## The semantics of each op, as `simp` lemmas

Stated with the argument vectors typed as `denote` sees them (`DialectSignature.sig op`), so
`simp` matches them in a program's denotation. -/

section Denote
local notation "Args" op => HVector toType (DialectSignature.sig (d := CF) op)
local notation "Regs" op => HVector RegFn (DialectSignature.regSig (d := CF) op)

@[simp] theorem denote_cst (k : Nat) (r : Regs (.cst k)) :
    DialectDenote.denote (d := CF) (.cst k) (no_index (.nil : Args (.cst k))) r =
      (.cons (k : Nat) .nil : HVector toType [Ty.nat]) := rfl
@[simp] theorem denote_add (a b : Nat) (r : Regs .add) :
    DialectDenote.denote (d := CF) .add (no_index (.cons a (.cons b .nil) : Args .add)) r =
      (.cons (a + b) .nil : HVector toType [Ty.nat]) := rfl
@[simp] theorem denote_sub (a b : Nat) (r : Regs .sub) :
    DialectDenote.denote (d := CF) .sub (no_index (.cons a (.cons b .nil) : Args .sub)) r =
      (.cons (a - b) .nil : HVector toType [Ty.nat]) := rfl
@[simp] theorem denote_mul (a b : Nat) (r : Regs .mul) :
    DialectDenote.denote (d := CF) .mul (no_index (.cons a (.cons b .nil) : Args .mul)) r =
      (.cons (a * b) .nil : HVector toType [Ty.nat]) := rfl
@[simp] theorem denote_eqz (a : Nat) (r : Regs .eqz) :
    DialectDenote.denote (d := CF) .eqz (no_index (.cons a .nil : Args .eqz)) r =
      (.cons (if a = 0 then 1 else 0 : Nat) .nil : HVector toType [Ty.nat]) := rfl
@[simp] theorem denote_ite (ts rs : List Ty) (c : Nat) (xs : HVector toType ts) (thn els) :
    DialectDenote.denote (d := CF) (.ite ts rs) (no_index (.cons c xs : Args (.ite ts rs)))
      (no_index (.cons thn (.cons els .nil) : Regs (.ite ts rs))) =
      if c ≠ 0 then thn (Valuation.ofHVector xs) else els (Valuation.ofHVector xs) := rfl
@[simp] theorem denote_while (ts : List Ty) (xs : Args (.while ts)) (body) :
    DialectDenote.denote (d := CF) (.while ts) (no_index xs) (no_index (.cons body .nil : Regs (.while ts))) =
      whileLoop (fun st => (body (Valuation.ofHVector st)).map fun r => (r.head, r.tail))
        (xs : HVector toType ts) := rfl
@[simp] theorem denote_funcs (sigs : List (Nat × Nat)) (ts rs : List Ty) (xs : Args (.funcs sigs ts rs))
    (main regs) :
    DialectDenote.denote (d := CF) (.funcs sigs ts rs) (no_index xs) (no_index (.cons main regs : Regs (.funcs sigs ts rs))) =
      main (Valuation.ofHVector (fnVals (funcsFix fun T => bodies sigs T sigs regs) sigs ++
        (xs : HVector toType ts))) := rfl
@[simp] theorem denote_call (n m : Nat) (fv : List Nat → Option (List Nat)) (xs : HVector toType (nats n))
    (r : Regs (.call n m)) :
    DialectDenote.denote (d := CF) (.call n m) (no_index (.cons fv xs : Args (.call n m))) r =
      (fv (toNats xs)).bind (ofNats m) := rfl

end Denote

end RegionCF
