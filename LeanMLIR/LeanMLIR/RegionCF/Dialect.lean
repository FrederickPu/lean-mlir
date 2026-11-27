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

## Argument order

The dialect follows LeanMLIR's binder convention (that of its parser and printer): a list of
binders is a context read backwards. A region `^bb(%x₀, …, %xₖ)` has context `[xₖ, …, x₀]`,
and the results `%r₀, …, %rₖ = op …` are the op's results `[rₖ, …, r₀]`. So that each
binder means the operand or result at its position, a region op passes its operands to its
regions reversed (`rev`), and returns its regions' results reversed: a region's context is
`⟨ts.reverse⟩`, an op's results `rs.reverse`. Operands and `return` are in order.
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

/-- Reverse a vector onto another (as `List.reverseAux`, so the types agree by `rfl`). -/
def revAux {α : Type} {A : α → Type} : {as bs : List α} → HVector A as → HVector A bs →
    HVector A (as.reverseAux bs)
  | [], _, .nil, acc => acc
  | a :: as, bs, .cons x xs, acc => revAux (as := as) (bs := a :: bs) xs (.cons x acc)

/-- Reverse a vector. -/
def rev {α : Type} {A : α → Type} {as : List α} (xs : HVector A as) : HVector A as.reverse :=
  revAux xs .nil

inductive Op
  | cst (k : Nat)
  | add | sub | mul
  /-- `1` if the argument is `0`, else `0`. -/
  | eqz
  | ite (ts rs : List Ty)
  | while (ts : List Ty)
  | funcs (sigs : List (Nat × Nat)) (ts rs : List Ty)
  | call (n m : Nat)
  deriving Repr, DecidableEq

abbrev CF : Dialect where
  Op := Op
  Ty := Ty
  m := Option

instance : DialectSignature CF where
  signature
    | .cst _ => ⟨[], [], [.nat], .pure⟩
    | .eqz => ⟨[.nat], [], [.nat], .pure⟩
    | .ite ts rs => ⟨.nat :: ts, [(⟨ts.reverse⟩, rs), (⟨ts.reverse⟩, rs)], rs.reverse, .impure⟩
    | .while ts => ⟨ts, [(⟨ts.reverse⟩, .nat :: ts)], ts.reverse, .impure⟩
    | .funcs sigs ts rs =>
      ⟨ts, (⟨(fnTys sigs ++ ts).reverse⟩, rs) ::
          sigs.map (fun (n, m) => (⟨(fnTys sigs ++ nats n).reverse⟩, nats m)),
        rs.reverse, .impure⟩
    | .call n m => ⟨.fn n m :: nats n, [], (nats m).reverse, .impure⟩
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
    HVector RegFn (sigs.map fun (n, m) => (⟨(fnTys sigs₀ ++ nats n).reverse⟩, nats m)) → FnTable
  | [], .nil => fun _ _ => none
  | (n, _) :: sigs, .cons r rs => fun i xs =>
    if i = 0 then
      (ofNats n xs).bind fun ys =>
        (r (Valuation.ofHVector (rev (fnVals T sigs₀ ++ ys)))).map toNats
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
      (if c ≠ 0 then thn (Valuation.ofHVector (rev xs)) else els (Valuation.ofHVector (rev xs))).map rev
    | .while _, xs, .cons body .nil =>
      (whileLoop (fun st => (body (Valuation.ofHVector (rev st))).map fun r => (r.head, r.tail))
        xs).map rev
    | .funcs sigs _ _, xs, .cons main rs =>
      (main (Valuation.ofHVector
        (rev (fnVals (funcsFix fun T => bodies sigs T sigs rs) sigs ++ xs)))).map rev
    | .call _ m, .cons (f : List Nat → Option (List Nat)) xs, _ =>
      ((f (toNats xs)).bind (ofNats m)).map rev

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
      (if c ≠ 0 then thn (Valuation.ofHVector (rev xs))
        else els (Valuation.ofHVector (rev xs))).map rev := rfl
@[simp] theorem denote_while (ts : List Ty) (xs : Args (.while ts)) (body) :
    DialectDenote.denote (d := CF) (.while ts) (no_index xs) (no_index (.cons body .nil : Regs (.while ts))) =
      (whileLoop (fun st => (body (Valuation.ofHVector (rev st))).map fun r => (r.head, r.tail))
        (xs : HVector toType ts)).map rev := rfl
@[simp] theorem denote_funcs (sigs : List (Nat × Nat)) (ts rs : List Ty) (xs : Args (.funcs sigs ts rs))
    (main regs) :
    DialectDenote.denote (d := CF) (.funcs sigs ts rs) (no_index xs) (no_index (.cons main regs : Regs (.funcs sigs ts rs))) =
      (main (Valuation.ofHVector (rev (fnVals (funcsFix fun T => bodies sigs T sigs regs) sigs ++
        (xs : HVector toType ts))))).map rev := rfl
@[simp] theorem denote_call (n m : Nat) (fv : List Nat → Option (List Nat)) (xs : HVector toType (nats n))
    (r : Regs (.call n m)) :
    DialectDenote.denote (d := CF) (.call n m) (no_index (.cons fv xs : Args (.call n m))) r =
      ((fv (toNats xs)).bind (ofNats m)).map rev := rfl

end Denote

end RegionCF
