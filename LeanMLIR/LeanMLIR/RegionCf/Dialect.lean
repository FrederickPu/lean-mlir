/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework
import LeanMLIR.RegionCf.Fix

/-!
# `RegionCf d`: structured control flow over a base dialect `d`

`RegionCf d` extends a dialect `d` of region-free ops (its arithmetic) with control flow,
all as region ops, inside LeanMLIR's SSA, with no other IR (cf. `ScfFunctor`):

* `coe o`: an op `o` of `d`;
* `ite ts rs`: if-then-else, one region per branch;
* `while ts`: a loop; its body returns a flag (false: stop, the `break`) and the new state;
* `funcs sigs ts rs`: a group of mutually recursive functions `f₀ … fₖ`, `fᵢ` taking values
  of types `sigsᵢ.1` and returning values of types `sigsᵢ.2`. Its regions: first the code
  using them, then one body per function. Every region sees all the functions as values;
* `call ts us f xs`: apply a function value.

The dialect's monad is `Option`: a loop or a recursion that does not stop has no value.
Values are `d`'s values and functions. A function value takes and returns lists of `d`'s
values, each tagged with its type (`Val d`), and a call checks the types when it runs (a
mismatch has no value).

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

namespace RegionCfFunctor

/-! ## Types and values -/

/-- A value of a base type, tagged with its type. -/
abbrev Val (T : Type) [TyDenote T] := Σ t : T, toType t

/-- The types of `RegionCf d`: those of `d`, and functions. -/
inductive Ty (T : Type)
  | base (t : T)
  | fn
  deriving DecidableEq, Repr

instance {T : Type} [TyDenote T] : TyDenote (Ty T) where
  toType
    | .base t => toType t
    | .fn => List (Val T) → Option (List (Val T))

variable {T : Type}

/-- Base types. -/
abbrev bases (ts : List T) : List (Ty T) := ts.map .base

/-- The types of a group of functions. -/
abbrev fnTys (sigs : List (List T × List T)) : List (Ty T) := sigs.map fun _ => .fn

/-- The regions of a group's bodies, for its signatures `sigs₀`. -/
abbrev bodySig (sigs₀ sigs : List (List T × List T)) : List (Ctxt (Ty T) × List (Ty T)) :=
  sigs.map fun (a, r) => (⟨(fnTys sigs₀ ++ bases a).reverse⟩, bases r)

/-- Reverse a vector onto another (as `List.reverseAux`, so the types agree by `rfl`). -/
def revAux {α : Type} {A : α → Type} : {as bs : List α} → HVector A as → HVector A bs →
    HVector A (as.reverseAux bs)
  | [], _, .nil, acc => acc
  | a :: as, bs, .cons x xs, acc => revAux (as := as) (bs := a :: bs) xs (.cons x acc)

/-- Reverse a vector. -/
def rev {α : Type} {A : α → Type} {as : List α} (xs : HVector A as) : HVector A as.reverse :=
  revAux xs .nil

section Vals
variable [TyDenote T]

/-- Base values, as a vector of `d`'s values. -/
def unbase : {ts : List T} → HVector toType (bases ts) → HVector toType ts
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (unbase xs)

/-- `d`'s values, as base values. -/
def rebase : {ts : List T} → HVector toType ts → HVector toType (bases ts)
  | [], .nil => .nil
  | _ :: _, .cons x xs => .cons x (rebase xs)

/-- Base values as a list, each tagged with its type. -/
def toVals : {ts : List T} → HVector toType (bases ts) → List (Val T)
  | [], .nil => []
  | t :: _, .cons x xs => ⟨t, x⟩ :: toVals xs

variable [DecidableEq T]

/-- A list of values of the types `ts` (no value if a type differs). -/
def ofVals : (ts : List T) → List (Val T) → Option (HVector toType (bases ts))
  | [], [] => some .nil
  | t :: ts, ⟨u, x⟩ :: xs =>
    if h : u = t then (ofVals ts xs).map (.cons (h ▸ x : toType t)) else none
  | _, _ => none

end Vals

/-! ## Ops -/

/-- The ops of `RegionCf d`: those of `d` (`coe`), and control flow. -/
inductive Op (Op' T : Type)
  | coe (o : Op')
  | ite (ts rs : List (Ty T))
  | while (ts : List (Ty T))
  | funcs (sigs : List (List T × List T)) (ts rs : List (Ty T))
  | call (ts us : List T)
  deriving DecidableEq, Repr

/-- **Structured control flow over the dialect `d`.** -/
def RegionCf (d : Dialect) : Dialect where
  Op := Op d.Op d.Ty
  Ty := Ty d.Ty
  m := Option

/-- What `RegionCf d` needs of the base dialect `d`. -/
class Base (d : Dialect) [TyDenote d.Ty] [DialectSignature d] where
  /-- The type of `ite`'s condition and of `while`'s flag. -/
  condTy : d.Ty
  /-- When a condition holds, and a loop continues. -/
  isTrue : toType condTy → Bool
  /-- `d`'s ops have no regions. -/
  noRegions : ∀ o : d.Op, DialectSignature.regSig o = []
  /-- Run `d`'s effects (`some`, for a pure dialect). -/
  run {α : Type} : d.m α → Option α

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [Base d]

instance : Monad (RegionCf d).m := inferInstanceAs (Monad Option)
instance : LawfulMonad (RegionCf d).m := inferInstanceAs (LawfulMonad Option)
instance : TyDenote (RegionCf d).Ty := inferInstanceAs (TyDenote (Ty d.Ty))
instance [DecidableEq d.Ty] : DecidableEq (RegionCf d).Ty := inferInstanceAs (DecidableEq (Ty d.Ty))
instance [DecidableEq d.Op] [DecidableEq d.Ty] : DecidableEq (RegionCf d).Op :=
  inferInstanceAs (DecidableEq (Op d.Op d.Ty))

instance : DialectSignature (RegionCf d) where
  signature
    | .coe o => ⟨bases (DialectSignature.sig o), [], bases (DialectSignature.returnTypes o), .impure⟩
    | .ite ts rs =>
      ⟨.base (Base.condTy (d := d)) :: ts, [(⟨ts.reverse⟩, rs), (⟨ts.reverse⟩, rs)], rs.reverse, .impure⟩
    | .while ts => ⟨ts, [(⟨ts.reverse⟩, .base (Base.condTy (d := d)) :: ts)], ts.reverse, .impure⟩
    | .funcs sigs ts rs =>
      ⟨ts, (⟨(fnTys sigs ++ ts).reverse⟩, rs) ::
          bodySig sigs sigs,
        rs.reverse, .impure⟩
    | .call ts us => ⟨.fn :: bases ts, [], (bases us).reverse, .impure⟩

/-! ## Functions -/

section Functions
variable {T : Type} [TyDenote T]

/-- The function values of a table, for a group of signatures (function `i` is `Tb i`). -/
def fnVals (Tb : FnTable (Val T)) :
    (sigs : List (List T × List T)) → (i : Nat := 0) → HVector toType (fnTys sigs)
  | [], _ => .nil
  | _ :: sigs, i => .cons (Tb i : toType (Ty.fn (T := T))) (fnVals Tb sigs (i + 1))

/-- A region, as `denote` receives it. -/
abbrev RegFn (t : Ctxt (Ty T) × List (Ty T)) := t.1.Valuation → Option (HVector toType t.2)

variable [DecidableEq T]

/-- The bodies of a group, as a table transformer: function `i` runs region `i` on the
functions of `Tb` and its arguments. -/
def bodies (sigs₀ : List (List T × List T)) (Tb : FnTable (Val T)) :
    (sigs : List (List T × List T)) → HVector RegFn (bodySig sigs₀ sigs) → FnTable (Val T)
  | [], .nil => fun _ _ => none
  | (a, _) :: sigs, .cons r rs => fun i xs =>
    if i = 0 then
      (ofVals a xs).bind fun ys =>
        (r (Valuation.ofHVector (rev (fnVals Tb sigs₀ ++ ys)))).map toVals
    else bodies sigs₀ Tb sigs rs (i - 1) xs

end Functions

/-! ## Semantics -/

variable [DecidableEq d.Ty] [DialectDenote d] [Monad d.m]

/-- No regions, for an op of `d`. -/
def noRegs (o : d.Op) :
    HVector (fun t : Ctxt d.Ty × List d.Ty => t.1.Valuation → EffectKind.impure.toMonad d.m (HVector toType t.2))
      (DialectSignature.regSig o) :=
  (Base.noRegions o).symm ▸ .nil

/-- An op of `d`, on base values. -/
def coeDenote (o : d.Op) (xs : HVector toType (bases (DialectSignature.sig o))) :
    Option (HVector toType (bases (DialectSignature.returnTypes o))) :=
  (Base.run (EffectKind.liftEffect (EffectKind.le_impure _)
    (DialectDenote.denote o (unbase xs) (noRegs o)))).map rebase

instance : DialectDenote (RegionCf d) where
  denote
    | .coe o, xs, _ => coeDenote o xs
    | .ite _ _, .cons c xs, .cons thn (.cons els .nil) =>
      (if Base.isTrue (d := d) c then thn (Valuation.ofHVector (rev xs))
        else els (Valuation.ofHVector (rev xs))).map rev
    | .while _, xs, .cons body .nil =>
      (whileLoop (fun st => (body (Valuation.ofHVector (rev st))).map
        fun r => (Base.isTrue (d := d) r.head, r.tail)) xs).map rev
    | .funcs sigs _ _, xs, .cons main rs =>
      (main (Valuation.ofHVector
        (rev (fnVals (funcsFix fun Tb => bodies sigs Tb sigs rs) sigs ++ xs)))).map rev
    | .call _ us, .cons (f : List (Val d.Ty) → Option (List (Val d.Ty))) xs, _ =>
      ((f (toVals xs)).bind (ofVals us)).map rev

end RegionCfFunctor
