# Parse ops with regions from MLIR syntax

## Summary

LeanMLIR's generic MLIR parser (`[mlir_region| …]` → `mkCom`) could not handle any op with
regions: `Op.mkExprOf` panics on them (`-- TODO: parse regions`). Every region dialect in the
repo, such as `ScfFunctor` and PaperExamples' `iterate`, therefore builds its programs by hand.

This PR makes region ops parseable:

1. **Fix `Prod.foldToExpr`** (`Framework/ToExpr.lean`). It built the wrong term, so no
   in-memory program containing a region op could be turned back into a Lean term.
2. **Add `Op.mkRegions` and `Op.mkExprWithRegions`** (`MLIRSyntax/Transform/Utils.lean`).
   They are generic parsing for an op's regions, and the counterpart of `mkExprOf` for ops
   with regions.

Existing behavior is unchanged. `mkExprOf` is untouched, and no existing call site is
modified.

## 1. The `Prod.foldToExpr` bug

`Regions.toExprAux` uses `Prod.foldToExpr` to build each region's signature entry, a pair
`(context, return types)`. The old definition built the *type* instead of the pair:

```lean
-- before: `Prod.{1,1} α β a b`, the type constructor applied to 4 arguments, at universe 1
Function.uncurry <| mkApp4 (.const ``Prod [1,1]) α β
-- after: `Prod.mk a b`, with the right types and universes (checked by Qq)
fun (a, b) => q(($a, $b))
```

Elaborating any parsed program with a region op failed with
`function expected: @Prod (Ctxt _) (List _) …`. The bug never showed up before because
`Regions.toExprAux` only runs on an op with at least one region, which until now only an
in-memory transformation could produce. The call site now also passes `α`/`β` explicitly,
so the types don't depend on inference.

## 2. Generic region parsing

```lean
def mkRegions (mkRegion : Region φ → ExceptM d (Σ Γ eff ty, Com d Γ eff ty)) :
    (regs : List (Region φ)) → (regSig : RegionSignature d.Ty) →
      ExceptM d (HVector (fun t => Com d t.1 .impure t.2) regSig)

def Op.mkExprWithRegions (Γ : Ctxt d.Ty) (parsedOp : d.Op)
    (mkRegion : Region φ → ExceptM d (Σ Γ eff ty, Com d Γ eff ty))
    (args? : Option (ParsedArgs Γ) := none) :
    ReaderM d (Σ eff returnTy, Expr d Γ eff returnTy)
```

`mkRegions` translates each region with `mkRegion`, checks it against the op's region
signature (the context and the return types), and lifts it to `.impure`, as `Expr.regArgs`
requires. A mismatch is an error, not a panic:

```
Region `bb0` has arguments [!nat, !nat], but its op expects [!nat]
Expected 1 region(s), but found 2
```

`mkRegion` is a parameter because a region contains ops of the same dialect, so translating
it needs the dialect's own `mkExpr`. In practice it is `mkCom`. A dialect ties the knot with
a `partial def`:

```lean
partial def mkExpr (Γ : Ctxt Ty) (op : MLIR.AST.Op 0) : ReaderM D (Σ eff ty, Expr D Γ eff ty) := do
  let _ : LeanMLIR.DialectParse D 0 := { mkTy, isValidReturn, mkExpr := fun Γ op => mkExpr Γ op }
  let mkRegion : Region 0 → ExceptM D (Σ Γ eff ty, Com D Γ eff ty) := mkCom
  match op.name with
  | "d.foo" => op.mkExprWithRegions (d := D) Γ .foo mkRegion
  | …
```

With `mkCom`, a region is parsed as a program of its own. It sees only its block arguments,
not the enclosing names, as for MLIR's `IsolatedFromAbove` ops. That matches `Expr`, whose
regions have their own context rather than extending the enclosing one. Using an outer name
inside a region is reported as `Undeclared name`.

## Testing

Proposed new test file, `LeanMLIR/Tests/RegionParse.lean`. It defines a small dialect with
one region op, `twice(x) { f } = f (f x)`, parses a program using it, and checks the result.
This is the exact file I ran, and it passes:

```lean
import LeanMLIR.MLIRSyntax.EDSL2
import LeanMLIR.MLIRSyntax.Transform.Utils

open MLIR.AST

namespace RegionParseTest

inductive Ty | int deriving DecidableEq, Repr, Lean.ToExpr
instance : TyDenote Ty where toType | .int => Nat
instance : ToString Ty where toString | .int => "i64"

inductive Op | cst (k : Nat) | add | twice deriving DecidableEq, Repr, Lean.ToExpr

abbrev Toy : Dialect where
  Op := Op
  Ty := Ty

instance : DialectSignature Toy where
  signature
    | .cst _ => ⟨[], [], [.int], .pure⟩
    | .add => ⟨[.int, .int], [], [.int], .pure⟩
    | .twice => ⟨[.int], [(⟨[.int]⟩, [.int])], [.int], .impure⟩

instance : DialectDenote Toy where
  denote
    | .cst k, _, _ => (.cons (k : Nat) .nil : HVector TyDenote.toType [Ty.int])
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil), _ =>
      (.cons (a + b) .nil : HVector TyDenote.toType [Ty.int])
    | .twice, .cons x .nil, .cons f .nil =>
      let g := fun (y : TyDenote.toType Ty.int) => (f (Ctxt.Valuation.nil.cons y)).head
      (.cons (g (g x)) .nil : HVector TyDenote.toType [Ty.int])

instance : DialectToExpr Toy where
  toExprDialect := .const ``Toy []
  toExprM := .const ``Id [0]

def mkTy : MLIRType 0 → ExceptM Toy Ty
  | .int .Signless (.concrete 64) => return .int
  | _ => throw <| .generic "expected i64"

def isValidReturn (_ : Ctxt Ty) (op : MLIR.AST.Op 0) : ReaderM Toy Bool :=
  return op.name == "return"

partial def mkExpr (Γ : Ctxt Ty) (op : MLIR.AST.Op 0) :
    ReaderM Toy (Σ eff ty, Expr Toy Γ eff ty) := do
  let _ : LeanMLIR.DialectParse Toy 0 := { mkTy, isValidReturn, mkExpr := fun Γ op => mkExpr Γ op }
  let mkRegion : Region 0 → ExceptM Toy (Σ Γ eff ty, Com Toy Γ eff ty) := mkCom
  match op.name with
  | "toy.cst" =>
    let (k, _) ← op.getIntAttr "value"
    op.mkExprOf (d := Toy) Γ (.cst k.toNat)
  | "toy.add" => op.mkExprOf (d := Toy) Γ .add
  | "toy.twice" => op.mkExprWithRegions (d := Toy) Γ .twice mkRegion
  | name => throw <| .unsupportedOp name

instance : LeanMLIR.DialectParse Toy 0 := { mkTy, isValidReturn, mkExpr }

elab "[toy| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg Toy

/-- `twice(x) { y + 3 }` is `x + 6`. -/
def prog := [toy| {
  ^bb0(%x : i64):
    %r = "toy.twice"(%x) ({
      ^bb0(%y : i64):
        %c = "toy.cst"() {value = 3} : () -> (i64)
        %s = "toy.add"(%y, %c) : (i64, i64) -> (i64)
        "return"(%s) : (i64) -> ()
    }) : (i64) -> (i64)
    "return"(%r) : (i64) -> ()
}]

#guard (show Nat from (prog.denote (Ctxt.Valuation.nil.cons (10 : Nat))).head) == 16

end RegionParseTest
```

Other checks done on the `blockir` branch:

- All modules of the `LeanMLIR` package build, except two that fail for unrelated reasons:
  `LeanMLIR.Dialects.LLVM.*` imports the `SSA` package, which the `LeanMLIR` package does
  not depend on, and `LeanMLIR/Examples.lean` is marked out of date in its own header.
  (Checked on `blockir`, not on a clean `main` checkout.)
- A larger dialect with loops, branches and mutually recursive functions (`RegionCf`, on
  branch `blockir`) parses, prints back and evaluates through these functions.

## Notes for reviewers

- **Block-argument order is unchanged.** As before, `mkCom` gives a region `^bb(%x₀, …, %xₖ)`
  the context `[xₖ, …, x₀]`, so a region signature should list its context in that order.
  This only matters for regions with several arguments.
- **A separate, existing issue, not fixed here.** For an op with several results,
  `mkComHelper` binds `%r₀, …, %rₖ = op` to the results `[rₖ, …, r₀]`, while the context is
  `ty ++ Γ`. Each name is then type-checked against the reversed position, so an op whose
  results have *different* types fails to type-check in syntax. Ops with same-typed results
  parse, but with the names reversed. Changing this would change the meaning of existing
  multi-result programs (DC, Handshake), so it deserves its own issue.

## Making the branch

The two files differ from `main` only by this change:

```sh
git switch -c region-parsing main
git checkout blockir -- LeanMLIR/LeanMLIR/Framework/ToExpr.lean \
                        LeanMLIR/LeanMLIR/MLIRSyntax/Transform/Utils.lean
# add LeanMLIR/LeanMLIR/Tests/RegionParse.lean (above), and import it from LeanMLIR/LeanMLIR/Tests.lean
```
