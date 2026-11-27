# RegionCf handoff

`RegionCf d` is structured control flow over a base dialect `d`: if, loops that may not
terminate, and mutually recursive first-class functions. It is built entirely from
**region ops** in LeanMLIR's existing SSA framework (`Com`/`Expr`), with no separate IR, as
upstream's `SSA/Projects/Scf/ScfFunctor.lean` does for `scf`. Loops and recursion are Lean
functions defined as fixpoints in `Option`, where "no value" means the program does not
terminate.

Names: the dialect is `RegionCf d`, everything lives in the namespace `RegionCfFunctor`, and
the files in `LeanMLIR/LeanMLIR/RegionCf/`. The ops print and parse as `"cf.ite"`, `"cf.while"`,
`"cf.funcs"`, `"cf.call"`. This is not MLIR's `cf` dialect, which is branch-based (`cf.br`).

Status: everything below builds with no errors, warnings or `sorry`, on branch `blockir`.

## Build

```sh
cd LeanMLIR
timeout 900 lake build LeanMLIR.RegionCf      # every module below (LeanMLIR/RegionCf.lean)
timeout 300 lake env lean --memory=4096 --threads=2 SomeScratch.lean
```

Always cap Lean runs (memory, threads, `timeout`, heartbeats ≤ 1000000), because a runaway
`rfl` or `whnf` can freeze the machine. Run `lake build <module>` before `lake env lean` on a
file that imports a changed module: `lake env lean` uses the built `.olean`s, and a stale
one gives confusing errors (for example, a lemma about a dialect that no longer exists).

On a fresh checkout: no Mathlib binary cache exists for this nightly Mathlib revision
(`lake exe cache get` finds nothing), so the first build compiles ~670 modules from source.
If lake fails with `git exited with code 128` on a package, `git fetch origin <rev>` inside
`.lake/packages/<pkg>` and check out the pinned revision by hand.

Known failures in this package that predate RegionCf: `LeanMLIR.Dialects.LLVM.*` imports the
`SSA` package (so `lake build` of the default target fails), and `LeanMLIR/Examples.lean`
is marked out of date in its own header.

## Files

| File | What it is |
|---|---|
| `Fix.lean` | The fixpoints. `whileLoop` (via `partial_fixpoint`, a `Bool` flag: `false` breaks) and `whileLoop_unfold`. `FnTable V := Nat → List V → Option (List V)`. `funcsFix F` is the least fixpoint, defined with `Lean.Order.fix` when `F` is monotone (a classical `if`) and `implemented_by` a `partial def` so programs still run. `funcsFix_unfold`. **`whileLoop_inv`**: a loop with an invariant and a decreasing measure stops, in a state satisfying a postcondition. **`whileLoop_diverges`**: a loop that always continues from an invariant has no value. |
| `Dialect.lean` | **`RegionCf d`**, with monad `Option`. The class **`Base d`**: the condition/flag type `condTy` and `isTrue`, `noRegions` (base ops have none), `run` (the base monad into `Option`). Types `Ty T := base t | fn`; a function value is `List (Val T) → Option (List (Val T))`, `Val T := Σ t, ⟦t⟧`. Ops `coe o`, `ite ts rs`, `while ts`, `funcs sigs ts rs`, `call ts us`. Helpers `bases`, `fnTys`, `bodySig`, `rev`, `unbase`/`rebase`, `toVals`/`ofVals`, `fnVals`, `bodies`, `coeDenote`. |
| `Mono.lean` | **The general monotonicity theorem**, `funcsFix_bodies_unfold`, the per-function equation `funcsFix_apply`, and simp lemmas `bodies_zero`/`_succ`, `ofVals_*`, `toVals_*`, `fnVals_*`. |
| `Simp.lean` | Lookup lemmas for literal variable indices, the **`cf_reduce`** tactic, and **`cf_simp`** (`cf_reduce` plus the `Option` bind/map normalization it leaves to do). |
| `Syntax.lean` | MLIR syntax for any `RegionCf d` whose `d` has a `DialectParse`: `ToExpr`, `DialectToExpr`, `DialectParse`, `DialectPrint` (`#eval prog` prints it back), and `elabRegion`. Ops other than the four control-flow ones go to `d`'s own parser. |
| `Arith.lean` | The examples' base dialect: natural-number arithmetic (`arith.cst/add/sub/mul/eqz`, type `!nat`, monad `Id`), its `Base` instance (nonzero is true), its syntax, and the elaborators **`[cf| …]`** and **`[cf_region| …]`** for `RegionCf Arith`. |
| `MutualRec.lean` | Worked example: `funcs { f; g } in f(n)`, proved equal to a Lean `mutual` definition. |
| `Loop.lean` | Worked example: Fibonacci as a `while` whose body is an `ite` (continue, or break), proved equal to a Lean `fib`. Also `spin`, a loop that never stops, and `spin_none`. |
| `Nested.lean` | Worked example: `n * m` by a loop nested in a loop, proved with `whileLoop_inv` for each loop. |
| `FuncLoop.lean` | Worked example: `funcs { sq; sumsq }` where `sumsq`'s body is a loop calling `sq` (passed in the loop state), proved equal to `1² + … + n²`. |
| `MainlinePR.md` | The description of a PR to `main` for the shared-code changes below. |

`LeanMLIR/RegionCf.lean` imports everything, and the root `LeanMLIR.lean` imports it.

Shared code added or fixed for this (outside `RegionCf/`), see `MainlinePR.md`:
- `MLIRSyntax/Transform/Utils.lean`: `Op.mkRegions` and `Op.mkExprWithRegions`, the generic
  parsing of an op's regions (each by a given translator, usually `mkCom`, so regions are
  isolated from above). Before, `mkExprOf` panicked on ops with regions.
- `Framework/ToExpr.lean`: `Prod.foldToExpr` built `Prod α β a b` (the type, at universe 1)
  instead of `Prod.mk a b`, so no parsed program with a region op could be turned into a term.

## Using it with another base dialect

A base dialect `d` needs: `TyDenote`, `DialectSignature`, `DialectDenote` (all ops
region-free), `DecidableEq` on its types and ops, `Monad d.m`, and a `Base d` instance. For
syntax it also needs `ToExpr`/`DialectToExpr`, `ToString`/`Repr` on its types, a
`DialectParse d 0`, a `DialectPrint d`, and one line per elaborator:

```lean
elab "[foo| " reg:mlir_region "]" : term => SSA.elabIntoCom' reg (RegionCf Foo)
elab "[foo_region| " reg:mlir_region "]" : term => elabRegion (d := Foo) reg
```

`Arith.lean` is the template. `cf_reduce` unfolds definitions in a fixed list of namespaces
(`CFReduce.unfoldable`), which includes `RegionCfFunctor`. A base dialect defined elsewhere
may need its namespace added there.

## Syntax

```
def bodyAst : MLIR.AST.Region 0 := [mlir_region| { ^bb0(%n : !nat, …): … }]
def body := [cf_region| $(bodyAst)]          -- the region, to state lemmas about
def prog := [cf| {
  ^bb0(%n : !nat):
    %c0 = "arith.cst"() {value = 0} : () -> (!nat)
    %n', %a, %b = "cf.while"(%n, %c0, %c1) ($(bodyAst)) : (!nat, !nat, !nat) -> (!nat, !nat, !nat)
    "return"(%a) : (!nat) -> ()
}]
```

- Types: the base dialect's (`!nat`), and `!fn` for a function value.
- Ops: `"cf.ite"`, `"cf.while"`, `"cf.funcs"`, `"cf.call"`; any other op is parsed by the
  base dialect's parser, on a context of the op's operands, and becomes `coe`. `"return"`
  ends a region.
- Op parameters are inferred: `ts` from operand types, `rs`/`us` from result types, a
  `funcs` group's signatures from each function region's block arguments (after the
  functions) and the types of its `return`.
- Regions see only their block arguments (an outer name is an `Undeclared name` error).
- Splicing a region (`$(bodyAst)`) is how to name a body for lemmas: `body` is then
  syntactically the region inside `prog`, up to unfolding `body` (so use `erw`).

## Semantics of the region ops

**Binder order.** LeanMLIR's parser and printer read a list of binders backwards: a region
`^bb(%x₀, …, %xₖ)` has context `[xₖ, …, x₀]`, and results `%r₀, …, %rₖ = op` are bound to
the op's results `[rₖ, …, r₀]` (that is how `mkComHelper` and `Expr.printResultList` work,
for every dialect). Operands and `return` are in order. So that every binder means the
operand or result at its position, the region ops pass their operands to a region reversed
(`Valuation.ofHVector (rev xs)`, region context `⟨ts.reverse⟩`) and return results reversed
(`.map rev`, result types `rs.reverse`). Hand-written programs must follow this too, and a
program's own arguments are given reversed (`Valuation.ofHVector (rev [n, m])` for
`^bb0(%n, %m)`).

- **`coe o`**: `o`'s denotation (`coeDenote`), run in `Option` by `Base.run`.
- **`ite ts rs`**: the first argument is the condition (`Base.isTrue`), and the other
  arguments `ts` go to whichever branch runs. Each branch region is `(⟨ts.reverse⟩, rs)`.
- **`while ts`**: the body region is `(⟨ts.reverse⟩, .base condTy :: ts)`: a flag, then the
  new state. The loop continues while `Base.isTrue flag`. Regions capture nothing, so
  anything the body needs, including functions, must be passed in the state.
- **`funcs sigs ts rs`**: the regions are the main region `(⟨(fnTys sigs ++ ts).reverse⟩, rs)`
  followed by one body per signature `(a, r)` (`bodySig`), of shape
  `(⟨(fnTys sigs ++ bases a).reverse⟩, bases r)`. Every region sees every function of the
  group as a value. The denotation is
  `(main (rev (fnVals (funcsFix fun Tb => bodies sigs Tb sigs regs) ++ xs))).map rev`.
- **`call ts us`**: applies a function value to base values of types `ts`
  (tagged: `toVals`). Results of other types or another number (`ofVals us`) give `none`.

## Key results

- **`Com.denote_mono`** (`Mono.lean`): every `RegionCf d` program is monotone. Values are
  ordered by how defined they are:
  - functions pointwise by `⊑` in `Option`;
  - base values only below themselves.

  The relations are `ValLe`/`HVLe`/`VLe`/`OptLe`, over any base type `T`. The proof is a
  mutual structural recursion that mirrors the framework's `denote`. Per-op cases are in
  `denote_mono`; `coe` is trivial (base arguments below each other are equal,
  `HVLe.bases_eq`). The `while` case uses `whileLoop_rel`, a fixpoint induction that works
  for any relation on loop states.
- **`bodies_monotone`**: if a group's bodies are monotone, the group is monotone in its table.
- **`funcsFix_bodies_unfold sigs regs`**: for any program, the table equals its bodies
  calling the table. This is the general reduction rule for mutual recursion, with no proof
  obligation left to the program.
- **`funcsFix_apply sigs rs hrs i xs`**: the table at any index `i`, unfolded once, for any
  regions `rs` with `RegsMono rs` (from `HVector.denote_mono (d := …) regs` for a program).
- **`F'_eq`** (`MutualRec.lean`): `F' n = some (f n)`. The proof pattern:
  1. `fBody_zero` / `fBody_succ` (and `g`'s): each body on `0` and on `n + 1`, the first by
     `rfl`, the second by `cf_simp`, then a case split on `ofVals [.nat] r`, the result of
     the call. Splitting on `n` this way avoids `n + 1 - 1` inside a tagged value
     `⟨.nat, …⟩`, which `simp` does not rewrite (its type is `⟦nat⟧`, not `Nat`).
  2. `T_f` / `T_g`: `(funcsFix_apply _ _ hFb i _).trans rfl`, where
     `hFb := HVector.denote_mono (d := Arith) bodyRegs`.
  3. `table`: induction on `n`, by `rw` with the body lemmas and the induction hypotheses,
     then `rfl`.
  4. `F'_eq`: `cf_reduce` reduces `prog`, then `erw` with `table`.
- **`Fib'_eq`** (`Loop.lean`): `step_eq` (by `rfl` on each case), `loop` by induction with
  `whileLoop_unfold`, then `cf_reduce`, `erw [loop …]`, `cf_reduce`, `iter_fib`.
- **`Mul'_eq`** (`Nested.lean`): per-loop step lemmas split into zero/successor cases (the
  outer successor step runs the inner loop: `cf_reduce`, `erw [inner_loop …]`, `rfl`), each
  loop by `whileLoop_inv` with the invariant and measure defined by pattern matching on the
  state vector (`innerInv`, `innerMeasure`; with `st.head`/`st.tail.head` instead, `omega`
  cannot see through the `match`es).
- **`Sumsq'_eq`** (`FuncLoop.lean`): the loop is proved for any function value `fv` with
  `IsSq fv` (`∀ i, fv [⟨.nat, i⟩] = some [⟨.nat, i * i⟩]`): in `step_succ`, `cf_reduce` stops
  at the call, `rw [hf]`, `rfl`. Then `T_sq : IsSq (T 0)` by `funcsFix_apply`, and `T_sumsq`
  by `funcsFix_apply` and the loop lemma.

## `cf_reduce` (Simp.lean)

`cf_reduce` rewrites the goal to a definitionally equal one. It reduces every data subterm
by unfolding its head while that makes progress, using `whnfCore` with
`unfoldDefinition?`/`unfoldProjInst?`. It is designed to stop at what is not known:

- it never unfolds into a `match` that is stuck (`isStuck`);
- it never unfolds `ite`/`dite`; `decideIte` picks a branch only when the condition
  decides (this is also how `ofVals`'s type checks and `Base.isTrue` flags evaluate);
- it never unfolds `funcsFix` or `whileLoop`;
- it leaves arithmetic and decision instances alone (`keptClass`, `isArith`);
- it skips function-typed, type, proof and instance subterms;
- it zeta-reduces at the end and runs at most 100 passes.

As a result, a call to an unknown function stays as `(gv [⟨.nat, n⟩]).bind …`, and the rest
evaluates. It is heuristic: it has been tested on the four examples only.

Pitfalls found along the way:
- Plain `simp` with the framework lemmas gets stuck on variable lookups. Literal `⟨i, h⟩`
  variables become `Var.last` over `Ctxt.ofList` contexts, which the framework lemmas do
  not match.
- `rfl` between two `Com.denote` terms can take forever. Normalize with `simp only` and
  `congr` first.
- `rw` with a lemma about the abbrev `T` fails because `T` hides the `funcsFix` head:
  restate it (`unfold T at h`, or state it about `funcsFix Fb …`).
- `cf_reduce` also reduces inside the `whileLoop`'s step function, so afterwards it no longer
  matches `step` syntactically: `rw [loop …]` fails, `erw` works.
- To build `RegsMono` for a concrete group, give the regions `HVector` its full type in a
  definition (`bodyRegs`, of type `HVector … (bodySig sigs sigs)`), and pass the base
  dialect to `HVector.denote_mono (d := Arith)`.
- `toVals`'s type list cannot be inferred from `bases ts` (a `List.map`): write
  `toVals (ts := [Arith.Ty.nat])`.
- `RegionCf` is a `def`, not an `abbrev`: as an `abbrev` it unfolds to a bare `Dialect.mk …`,
  and instances stated for `RegionCf d` no longer match `RegionCf Arith`. Its `Monad` and
  `TyDenote` instances are declared explicitly (as upstream does for `Scf`).
- Mutual theorems over `Com (RegionCf d) Γ .impure ty` are not structurally recursive,
  because the index is not a variable. Take `eff` with `heff : eff = .impure` instead, make
  the recursive calls before `subst heff`, and use `toOpt` for the result type.

## Remaining work

1. **Proof ergonomics.** Every proof needs `erw` after `cf_reduce`, because `cf_reduce` also
   reduces inside loop and function bodies (so they no longer match `step`, `fBody`, …
   syntactically). A `cf_reduce` that leaves the arguments of `whileLoop`/`funcsFix` alone
   would make plain `rw` work. Step lemmas per loop are still written by hand.
2. **Typed function values (optional).** Function values check their argument and result
   types when called (`ofVals`). Statically typed functions (`fn ts us`, denoted on
   `HVector`s) would need a dependently typed table for `funcsFix`.
3. **Base dialects with regions or effects.** `Base` requires region-free base ops and runs
   the base monad in `Option` (`run`). A base op with regions, or a base monad that cannot
   be run in `Option`, is not supported.
4. **Syntax polish (optional).** Only MLIR's generic op syntax is supported; a short syntax
   would be macros onto the same AST.
5. **Upstreaming.** See `MainlinePR.md`: `Prod.foldToExpr` (bug fix) and generic region
   parsing. Separately worth reporting: the framework's reversed result binding, under which
   a multi-result op whose result types differ does not typecheck in syntax.
6. Old BlockIR files from an earlier design exist in the repo but are unused; don't confuse
   them with this work.
