/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCf.Syntax

/-!
# `Arith`: a base dialect of natural-number arithmetic

The base dialect of the examples (`RegionCf Arith`): numbers, and pure, region-free ops.

* `cst k`: the constant `k`;
* `add`, `sub`, `mul`: `+`, truncated `-`, `*`;
* `eqz`: `1` if the argument is `0`, else `0`.

`RegionCf Arith`'s conditions and loop flags are numbers: nonzero means true.

Syntax: the type `!nat`; the ops `"arith.cst"` (attribute `value`), `"arith.add"`,
`"arith.sub"`, `"arith.mul"`, `"arith.eqz"`. `[cf| …]` elaborates a `RegionCf Arith` program,
`[cf_region| …]` a region on its own (see `RegionCfFunctor.elabRegion`).
-/

open Lean
open MLIR.AST
open TyDenote (toType)

namespace RegionCfFunctor.Arith

inductive Ty
  | nat
  deriving DecidableEq, Repr, Lean.ToExpr

instance : ToString Ty where
  toString | .nat => "!nat"

instance : TyDenote Ty where
  toType | .nat => Nat

inductive Op
  | cst (k : Nat)
  | add | sub | mul
  | eqz
  deriving DecidableEq, Repr, Lean.ToExpr

end Arith

/-- Natural-number arithmetic. -/
abbrev Arith : Dialect where
  Op := Arith.Op
  Ty := Arith.Ty

namespace Arith

instance : DialectSignature Arith where
  signature
    | .cst _ => ⟨[], [], [.nat], .pure⟩
    | .eqz => ⟨[.nat], [], [.nat], .pure⟩
    | .add | .sub | .mul => ⟨[.nat, .nat], [], [.nat], .pure⟩

instance : DialectDenote Arith where
  denote
    | .cst k, _, _ => (.cons (k : Nat) .nil : HVector toType [Ty.nat])
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a + b) .nil : HVector toType [Ty.nat])
    | .sub, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a - b) .nil : HVector toType [Ty.nat])
    | .mul, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a * b) .nil : HVector toType [Ty.nat])
    | .eqz, .cons (a : Nat) .nil, _ =>
      (.cons (if a = 0 then 1 else 0 : Nat) .nil : HVector toType [Ty.nat])

/-- Conditions and loop flags are numbers, nonzero meaning true. -/
instance : Base Arith where
  condTy := .nat
  isTrue c := (show Nat from c) != 0
  noRegions o := by cases o <;> rfl
  run x := some x

/-! ## Syntax -/

instance : DialectToExpr Arith where
  toExprDialect := .const ``RegionCfFunctor.Arith []
  toExprM := .const ``Id [0]

def mkTy : MLIRType 0 → ExceptM Arith Ty
  | .undefined "nat" => return .nat
  | ty => throw <| .generic s!"Unknown type `{repr ty}`: expected `!nat` or `!fn`"

def isValidReturn (_ : Ctxt Ty) (opStx : MLIR.AST.Op 0) : ReaderM Arith Bool :=
  return opStx.name == "return"

def mkExpr (Γ : Ctxt Ty) (opStx : MLIR.AST.Op 0) : ReaderM Arith (Σ eff ty, Expr Arith Γ eff ty) :=
  let _ : TransformTy Arith 0 := ⟨mkTy⟩
  match opStx.name with
  | "arith.cst" => do
    let (k, _) ← opStx.getIntAttr "value"
    if k < 0 then throw <| .generic s!"`arith.cst`: expected a natural number, found {k}"
    opStx.mkExprOf (d := Arith) Γ (.cst k.toNat)
  | "arith.add" => opStx.mkExprOf (d := Arith) Γ .add
  | "arith.sub" => opStx.mkExprOf (d := Arith) Γ .sub
  | "arith.mul" => opStx.mkExprOf (d := Arith) Γ .mul
  | "arith.eqz" => opStx.mkExprOf (d := Arith) Γ .eqz
  | name => throw <| .unsupportedOp s!"Unknown op `{name}`"

instance : LeanMLIR.DialectParse Arith 0 where
  mkTy := mkTy
  isValidReturn := isValidReturn
  mkExpr := mkExpr

instance : DialectPrint Arith where
  printOpName
    | .cst _ => "arith.cst" | .add => "arith.add" | .sub => "arith.sub"
    | .mul => "arith.mul" | .eqz => "arith.eqz"
  printTy := toString
  printAttributes
    | .cst k => s!"\{value = {k}}"
    | _ => ""
  dialectName := "arith"
  printReturn _ := "return"

/-- `[cf| { ^bb0(%x : !nat, …): … }]`: a `RegionCf Arith` program, in MLIR's generic syntax. -/
elab "[cf| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg (RegionCf Arith)

/-- `[cf_region| { … }]`: a `RegionCf Arith` region on its own (see `elabRegion`). -/
elab "[cf_region| " reg:mlir_region "]" : term => elabRegion (d := Arith) reg

end RegionCfFunctor.Arith
