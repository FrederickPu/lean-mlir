/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax.EDSL2
import LeanMLIR.MLIRSyntax.Transform.Utils
import LeanMLIR.RegionCf.Dialect

/-!
# Syntax for `RegionCf d`

Programs in MLIR's generic syntax, through LeanMLIR's generic parser (`mlir_region`),
`DialectParse`, and `SSA.elabIntoCom'`, for any base dialect `d` that has a `DialectParse`:

```
{
  ^bb0(%n : !nat):
    %c0 = "arith.cst"() {value = 0} : () -> (!nat)          -- an op of `d`
    %r = "cf.while"(%n) ({
      ^bb0(%k : !nat):
        …
        "return"(%flag, %k') : (!nat, !nat) -> ()
    }) : (!nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}
```

* Types: `d`'s types, and `!fn` for a function value.
* Ops: `"cf.ite"`, `"cf.while"`, `"cf.funcs"`, `"cf.call"`; any other op is parsed by `d`'s
  parser (on a context of its operands) and becomes `coe`. `"return"` ends a region.
* The ops' parameters are read off their operands, results and regions:
  - `"cf.ite"(%c, %xs…) ({then}, {else}) : … -> (rs…)`: `ite ts rs`, `ts` the types of `%xs`;
  - `"cf.while"(%xs…) ({body})`: `while ts`;
  - `"cf.funcs"(%xs…) ({main}, {f₀}, …, {fₖ}) : … -> (rs…)`: function `fᵢ`'s signature is its
    region's block arguments after the `k + 1` functions, and the types of its `return`;
  - `"cf.call"(%f, %xs…) : … -> (us…)`: `call ts us`.
* Regions are isolated from above: a region sees only its block arguments. Each is parsed
  as a program of its own (`mkCom`), through the generic `Op.mkExprWithRegions`.

A dialect `RegionCf d` gets its `[…| …]` elaborator from `SSA.elabIntoCom'` (see
`RegionCf/Arith.lean`), and `elabRegion` for a region on its own.
-/

open Lean Qq
open MLIR.AST
open Ctxt (Var Valuation)

namespace RegionCfFunctor

deriving instance Lean.ToExpr for Ty
deriving instance Lean.ToExpr for Op

instance {T : Type} [ToString T] : ToString (Ty T) where
  toString
    | .base t => toString t
    | .fn => "!fn"

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [Base d]
  [DecidableEq d.Ty] [DecidableEq d.Op] [ToString d.Ty] [Repr d.Ty]

instance : ToString (RegionCf d).Ty := inferInstanceAs (ToString (Ty d.Ty))
instance : Repr (RegionCf d).Ty := inferInstanceAs (Repr (Ty d.Ty))

instance [ToExpr d.Op] [ToExpr d.Ty] : ToExpr (RegionCf d).Op := inferInstanceAs (ToExpr (Op d.Op d.Ty))
instance [ToExpr d.Ty] : ToExpr (RegionCf d).Ty := inferInstanceAs (ToExpr (Ty d.Ty))

instance [ToExpr d.Op] [ToExpr d.Ty] [DialectToExpr d] : DialectToExpr (RegionCf d) where
  toExprDialect := mkApp (.const ``RegionCf []) (DialectToExpr.toExprDialect d)
  toExprM := .const ``Option [0]

/-! ## Types -/

variable [LeanMLIR.DialectParse d 0]

/-- `!fn`, and `d`'s types. -/
def mkTy : MLIRType 0 → ExceptM (RegionCf d) (Ty d.Ty)
  | .undefined "fn" => return .fn
  | ty => return .base (← (TransformTy.mkTy (d := d) ty : ExceptM d d.Ty))

instance : TransformTy (RegionCf d) 0 where
  mkTy := mkTy

/-- Base types (of `d`), or an error. -/
def unbaseTys (what : String) : List (Ty d.Ty) → ExceptM (RegionCf d) (List d.Ty)
  | [] => return []
  | .base t :: ts => return t :: (← unbaseTys what ts)
  | .fn :: _ => throw <| TransformError.generic s!"{what}: expected a value of the base dialect, found a function"

/-! ## Ops -/

def isValidReturn (_ : Ctxt (Ty d.Ty)) (opStx : MLIR.AST.Op 0) : ReaderM (RegionCf d) Bool :=
  return opStx.name == "return" || opStx.name == "cf.return"

/-- The signature of a function of a group, from its region: its block arguments after the
group's `k` functions, and the types its `return` returns. -/
def mkSig (k : Nat) (r : Region 0) : ExceptM (RegionCf d) (List d.Ty × List d.Ty) := do
  let args ← (r.args.drop k).mapM (TypedSSAVal.mkTy (d := RegionCf d))
  let some ret := r.ops.getLast?
    | throw <| TransformError.generic s!"`cf.funcs`: function region `{r.name}` is empty"
  let rets ← ret.args.mapM (TypedSSAVal.mkTy (d := RegionCf d))
  return (← unbaseTys "`cf.funcs`" args, ← unbaseTys "`cf.funcs`" rets)

/-- An op of `d`: parsed by `d`'s parser, on a context of the op's operands. -/
def mkBaseOp (opStx : MLIR.AST.Op 0) (argTys : List (Ty d.Ty)) : ExceptM (RegionCf d) d.Op := do
  let tys ← unbaseTys s!"`{opStx.name}`" argTys
  let names := opStx.args.map fun (v, _) => SSAValToString v
  let ⟨_, _, e⟩ ← (LeanMLIR.DialectParse.mkExpr (d := d) ⟨tys⟩ opStx |>.run names : ExceptM d _)
  return e.op

/-- Parse an op; its regions are parsed as programs of their own. -/
partial def mkExpr (Γ : Ctxt (Ty d.Ty)) (opStx : MLIR.AST.Op 0) :
    ReaderM (RegionCf d) (Σ eff ty, Expr (RegionCf d) Γ eff ty) := do
  let _ : LeanMLIR.DialectParse (RegionCf d) 0 :=
    { mkTy := mkTy, isValidReturn := isValidReturn, mkExpr := fun Γ op => mkExpr Γ op }
  let mkRegion : Region 0 → ExceptM (RegionCf d) (Σ Γ eff ty, Com (RegionCf d) Γ eff ty) := mkCom
  let args ← opStx.parseArgs Γ
  let resTys ← (opStx.res.mapM (TypedSSAVal.mkTy (d := RegionCf d)) : ExceptM (RegionCf d) _)
  let region (op : (RegionCf d).Op) :=
    opStx.mkExprWithRegions (d := RegionCf d) Γ op mkRegion (some args)
  match opStx.name with
  | "cf.ite" => region (.ite args.types.tail resTys)
  | "cf.while" => region (.while args.types)
  | "cf.funcs" =>
    let k := opStx.regions.length - 1
    let sigs ← ((opStx.regions.drop 1).mapM (mkSig k) : ExceptM (RegionCf d) _)
    region (.funcs sigs args.types resTys)
  | "cf.call" =>
    match args.types with
    | .fn :: ts =>
      region (.call (← unbaseTys "`cf.call`" ts) (← unbaseTys "`cf.call`" resTys))
    | _ => throw <| TransformError.generic "`cf.call`: expected a function as the first operand"
  | _ => opStx.mkExprOf (d := RegionCf d) Γ (.coe (← mkBaseOp opStx args.types)) (some args)

instance : LeanMLIR.DialectParse (RegionCf d) 0 where
  mkTy := mkTy
  isValidReturn := isValidReturn
  mkExpr := mkExpr

/-! ## Printing -/

instance [DialectPrint d] : DialectPrint (RegionCf d) where
  printOpName
    | .coe o => DialectPrint.printOpName (d := d) o
    | .ite .. => "cf.ite" | .while _ => "cf.while"
    | .funcs .. => "cf.funcs" | .call .. => "cf.call"
  printTy
    | .base t => DialectPrint.printTy (d := d) t
    | .fn => "!fn"
  printAttributes
    | .coe o => DialectPrint.printAttributes (d := d) o
    | _ => ""
  dialectName := "cf"
  printReturn _ := "return"

/-! ## Elaboration -/

/-- A region on its own: a program of effect `.impure`, as it is when a region of an op.

To prove things about a region on its own, define its syntax once and splice it in:
```
def bodyAst : MLIR.AST.Region 0 := [mlir_region| { ^bb0(…): … }]
abbrev body := [cf_region| $(bodyAst)]                    -- the region, to state lemmas
def prog := [cf| { … "cf.while"(…) ($(bodyAst)) … }]      -- the program using it
```
Both are elaborated from the same syntax, so `body` is exactly the region in `prog`. With
`body` an `abbrev`, a lemma about it rewrites (`rw`) in `prog` after `cf_reduce`. -/
def elabRegion [ToExpr d.Op] [ToExpr d.Ty] [DialectToExpr d] (reg : TSyntax `mlir_region) :
    Elab.TermElabM Lean.Expr := do
  let ⟨_, eff, _, com⟩ ← SSA.elabIntoComObj reg (RegionCf d)
  (com.changeEffect (EffectKind.le_impure eff)).toExprM

end RegionCfFunctor
