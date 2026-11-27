/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.MLIRSyntax.EDSL2
import LeanMLIR.MLIRSyntax.Transform.Utils
import LeanMLIR.RegionCf.Dialect

/-!
# Syntax for the `CF` dialect: `[cf| …]`

Programs in MLIR's generic syntax, through LeanMLIR's generic parser (`mlir_region`),
`DialectParse`, and `SSA.elabIntoCom'`:

```
[cf| {
  ^bb0(%n : !nat):
    %c0 = "cf.cst"() {value = 0} : () -> (!nat)
    %z = "cf.eqz"(%n) : (!nat) -> (!nat)
    %r = "cf.ite"(%z, %n) ({
      ^bb0(%m : !nat):
        "return"(%c0) : (!nat) -> ()       -- error: regions see no outer names
    }, { … }) : (!nat, !nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]
```

* Types: `!nat`, and `!fn_n_m` for `fn n m`.
* Ops: `"cf.cst"` (attribute `value`), `"cf.add"`, `"cf.sub"`, `"cf.mul"`, `"cf.eqz"`,
  `"cf.ite"`, `"cf.while"`, `"cf.funcs"`, `"cf.call"`; `"return"` ends a region.
* The ops' parameters are read off their operands, results and regions:
  - `"cf.ite"(%c, %xs…) ({then}, {else}) : … -> (rs…)`: `ite ts rs`, `ts` the types of `%xs`;
  - `"cf.while"(%xs…) ({body})`: `while ts`;
  - `"cf.funcs"(%xs…) ({main}, {f₀}, …, {fₖ}) : … -> (rs…)`: the signatures are the types
    of the first `k + 1` block arguments of `main` (one `!fn_n_m` per function);
  - `"cf.call"(%f, %xs…)`: `call n m`, from the type `!fn_n_m` of `%f`.
* Regions are isolated from above: a region sees only its block arguments. Each is parsed
  as a program of its own (`mkCom`), through the generic `Op.mkExprWithRegions`.
-/

open Lean Qq
open MLIR.AST
open Ctxt (Var Valuation)

namespace RegionCfFunctor

deriving instance Lean.ToExpr for Ty
deriving instance Lean.ToExpr for Op

instance : DialectToExpr CF where
  toExprDialect := .const ``CF []
  toExprM := .const ``Option [0]

instance : ToString Ty where
  toString
    | .nat => "!nat"
    | .fn n m => s!"!fn_{n}_{m}"

/-! ## Types -/

/-- `!nat`, and `!fn_n_m`. -/
def mkTy : MLIRType 0 → ExceptM CF Ty
  | .undefined "nat" => return .nat
  | .undefined s => do
    let err := TransformError.generic s!"Unknown type `!{s}`: expected `!nat` or `!fn_n_m`"
    match s.splitOn "_" with
    | ["fn", n, m] =>
      match n.toNat?, m.toNat? with
      | some n, some m => return .fn n m
      | _, _ => throw err
    | _ => throw err
  | ty => throw <| TransformError.generic s!"Unknown type `{repr ty}`: expected `!nat` or `!fn_n_m`"

instance : TransformTy CF 0 where
  mkTy := mkTy

/-! ## Ops -/

def isValidReturn (_ : Ctxt Ty) (opStx : MLIR.AST.Op 0) : ReaderM CF Bool :=
  return opStx.name == "return" || opStx.name == "cf.return"

/-- The signatures of a group of functions: the types of its first block arguments. -/
def mkSigs : List Ty → ExceptM CF (List (Nat × Nat))
  | [] => return []
  | .fn n m :: ts => return (n, m) :: (← mkSigs ts)
  | t :: _ => throw <| TransformError.generic s!"`cf.funcs`: expected a function type, found `{t}`"

/-- Parse an op; its regions are parsed as programs of their own. -/
partial def mkExpr (Γ : Ctxt Ty) (opStx : MLIR.AST.Op 0) : ReaderM CF (Σ eff ty, Expr CF Γ eff ty) := do
  let _ : LeanMLIR.DialectParse CF 0 :=
    { mkTy := RegionCfFunctor.mkTy, isValidReturn := isValidReturn, mkExpr := fun Γ op => mkExpr Γ op }
  let mkRegion : Region 0 → ExceptM CF (Σ Γ eff ty, Com CF Γ eff ty) := mkCom
  let args ← opStx.parseArgs Γ
  let resTys ← (opStx.res.mapM (TypedSSAVal.mkTy (d := CF)) : ExceptM CF _)
  let plain (op : Op) := opStx.mkExprOf (d := CF) Γ op (some args)
  let region (op : Op) := opStx.mkExprWithRegions (d := CF) Γ op mkRegion (some args)
  match opStx.name with
  | "cf.cst" =>
    let (k, _) ← opStx.getIntAttr "value"
    if k < 0 then throw <| TransformError.generic s!"`cf.cst`: expected a natural number, found {k}"
    plain (.cst k.toNat)
  | "cf.add" => plain .add
  | "cf.sub" => plain .sub
  | "cf.mul" => plain .mul
  | "cf.eqz" => plain .eqz
  | "cf.ite" => region (.ite args.types.tail resTys)
  | "cf.while" => region (.while args.types)
  | "cf.funcs" =>
    let some main := opStx.regions.head?
      | throw <| TransformError.generic "`cf.funcs`: expected a main region"
    let fnTys ← ((main.args.take (opStx.regions.length - 1)).mapM (TypedSSAVal.mkTy (d := CF)) :
      ExceptM CF _)
    region (.funcs (← mkSigs fnTys) args.types resTys)
  | "cf.call" =>
    match args.types with
    | .fn n m :: _ => region (.call n m)
    | _ => throw <| TransformError.generic "`cf.call`: expected a function as the first operand"
  | name => throw <| TransformError.unsupportedOp s!"Unknown op `{name}`"

instance : LeanMLIR.DialectParse CF 0 where
  mkTy := RegionCfFunctor.mkTy
  isValidReturn := isValidReturn
  mkExpr := mkExpr

/-! ## Printing -/

instance : DialectPrint CF where
  printOpName
    | .cst _ => "cf.cst" | .add => "cf.add" | .sub => "cf.sub" | .mul => "cf.mul"
    | .eqz => "cf.eqz" | .ite .. => "cf.ite" | .while _ => "cf.while"
    | .funcs .. => "cf.funcs" | .call .. => "cf.call"
  printTy := toString
  printAttributes
    | .cst k => s!"\{value = {k}}"
    | _ => ""
  dialectName := "cf"
  printReturn _ := "return"

/-- `[cf| { ^bb0(%x : !nat, …): … }]`: a `CF` program, in MLIR's generic syntax. -/
elab "[cf| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg CF

/-- `[cf_region| { … }]`: a `CF` program of effect `.impure`, as it is when a region of an op.

To prove things about a region on its own, define its syntax once and splice it in:
```
def bodyAst : MLIR.AST.Region 0 := [mlir_region| { ^bb0(…): … }]
def body := [cf_region| $(bodyAst)]                       -- the region, to state lemmas
def prog := [cf| { … "cf.while"(…) ($(bodyAst)) … }]      -- the program using it
```
Both are elaborated from the same syntax, so `body` is exactly the region in `prog`. -/
elab "[cf_region| " reg:mlir_region "]" : term => do
  let ⟨_, eff, _, com⟩ ← SSA.elabIntoComObj reg CF
  (com.changeEffect (EffectKind.le_impure eff)).toExprM

end RegionCfFunctor
