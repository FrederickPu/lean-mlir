# RegionCf handoff

Structured control flow (if, loops, mutually recursive functions) built entirely from
**region ops** in LeanMLIR's existing SSA framework (`Com`/`Expr`). There is no separate IR.
Loops and recursion are Lean functions defined as fixpoints in `Option`, where "no value"
means the program does not terminate.

Status: everything below builds with no errors, warnings or `sorry`, on branch `blockir`.

## Build

```sh
cd LeanMLIR
timeout 900 lake build LeanMLIR.RegionCf      # every module below (LeanMLIR/RegionCfFunctor.lean)
timeout 300 lake env lean --memory=4096 --threads=2 SomeScratch.lean
```

Always cap Lean runs (memory, threads, `timeout`, heartbeats ≤ 1000000), because a runaway
`rfl` or `whnf` can freeze the machine. Run `lake build <module>` before `lake env lean` on a
file that imports a new module, or the `.olean` will be missing.

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
| `Fix.lean` | The fixpoints. `whileLoop` (via `partial_fixpoint`) and `whileLoop_unfold`. `FnTable := Nat → List Nat → Option (List Nat)`. `funcsFix F` is the least fixpoint, defined with `Lean.Order.fix` when `F` is monotone (a classical `if`) and `implemented_by` a `partial def` so programs still run. `funcsFix_unfold (h : monotone F)`. **`whileLoop_inv`**: a loop with an invariant and a decreasing measure stops, in a state satisfying a postcondition. **`whileLoop_diverges`**: a loop that always continues from an invariant has no value (`none`). |
| `Dialect.lean` | The `CF` dialect, with monad `Option`, following LeanMLIR's binder order (see below). Types: `nat` and `fn n m` (denoted as `List Nat → Option (List Nat)`). Ops: `cst add sub mul eqz` (pure); `ite ts rs`, `while ts`, `funcs sigs ts rs`, `call n m` (impure). Helpers `toNats`, `ofNats`, `fnVals`, `bodies`, `rev` (an `HVector` reversed, `rfl`-typed via `revAux`). Simp lemmas `denote_*` and `effectKind_*`, one per op. |
| `Syntax.lean` | **`[cf| …]`**: programs in MLIR's generic syntax, through LeanMLIR's generic parser, `DialectParse`, `SSA.elabIntoCom'`. Also `[cf_region| …]` (a region on its own, effect `.impure`), `ToExpr`, `DialectToExpr`, and a `DialectPrint` (so `#eval prog` prints it back). |
| `Simp.lean` | Lookup lemmas for literal variable indices, the **`cf_reduce`** tactic, and **`cf_simp`** (`cf_reduce` plus the `Option` bind/map normalization it leaves to do). |
| `Mono.lean` | **The general monotonicity theorem**, `funcsFix_bodies_unfold`, and the per-function equation `funcsFix_apply` with simp lemmas `bodies_zero`/`bodies_succ`, `ofNats_*`, `toNats_*`, `fnVals_*`. |
| `MutualRec.lean` | Worked example, written in `[cf| …]`: `funcs { f; g } in f(n)`, proved equal to a Lean `mutual` definition. |
| `Loop.lean` | Worked example, written in `[cf| …]`: Fibonacci as a `while` whose body is an `ite` (continue, or break with flag `0`), proved equal to a Lean `fib`. |
| `Nested.lean` | Worked example: `n * m` by a loop nested in a loop (the outer body runs the inner `while`), proved with `whileLoop_inv` for each loop. |
| `FuncLoop.lean` | Worked example: `funcs { sq; sumsq }` where `sumsq`'s body is a loop that calls `sq` (passed in the loop state), proved equal to `1² + … + n²`. |

`Loop.lean` also has `spin`, a loop that never breaks, and `spin_none` (by `whileLoop_diverges`).
`LeanMLIR/RegionCfFunctor.lean` imports everything, and the root `LeanMLIR.lean` imports it.

Shared code added or fixed for this (outside `RegionCf/`):
- `MLIRSyntax/Transform/Utils.lean`: `Op.mkRegions` and `Op.mkExprWithRegions`, the generic
  parsing of an op's regions (each by a given translator, usually `mkCom`, so regions are
  isolated from above). Before, `mkExprOf` panicked on ops with regions.
- `Framework/ToExpr.lean`: `Prod.foldToExpr` built `Prod α β a b` (the type, at universe 1)
  instead of `Prod.mk a b`, so no parsed program with a region op could be turned into a term.

## Syntax

```
def bodyAst : MLIR.AST.Region 0 := [mlir_region| { ^bb0(%n : !nat, …): … }]
def body := [cf_region| $(bodyAst)]          -- the region, to state lemmas about
def prog := [cf| {
  ^bb0(%n : !nat):
    %c0 = "cf.cst"() {value = 0} : () -> (!nat)
    %n', %a, %b = "cf.while"(%n, %c0, %c1) ($(bodyAst)) : (!nat, !nat, !nat) -> (!nat, !nat, !nat)
    "return"(%a) : (!nat) -> ()
}]
```

- Types `!nat`, `!fn_n_m`. Ops `"cf.cst"` (attribute `value`), `"cf.add"`/`sub`/`mul`/`eqz`,
  `"cf.ite"`, `"cf.while"`, `"cf.funcs"`, `"cf.call"`; `"return"` ends a region.
- Op parameters are inferred: `ts` from operand types, `rs` from result types, a `funcs`
  group's signatures from the `!fn_n_m` types of its main region's first block arguments,
  `call n m` from its function operand's type.
- Regions see only their block arguments (an outer name is an `Undeclared name` error).
- Splicing a region (`$(bodyAst)`) is how to name a body for lemmas: `body` is then
  syntactically the region inside `prog`, up to unfolding `body` (so use `erw`).

## Semantics of the region ops

**Binder order.** LeanMLIR's parser and printer read a list of binders backwards: a region
`^bb(%x₀, …, %xₖ)` has context `[xₖ, …, x₀]`, and results `%r₀, …, %rₖ = op` are bound to
the op's results `[rₖ, …, r₀]` (that is how `mkComHelper` and `Expr.printResultList` work,
for every dialect). Operands and `return` are in order. So that every binder means the
operand or result at its position, the CF region ops pass their operands to a region
reversed (`Valuation.ofHVector (rev xs)`, region context `⟨ts.reverse⟩`) and return results
reversed (`.map rev`, result types `rs.reverse`). Hand-written programs must follow this too.

- **`ite ts rs`**: the first argument is the condition (nonzero means true), and the other
  arguments `ts` go to whichever branch runs. Each branch region is `(⟨ts.reverse⟩, rs)`.
- **`while ts`**: the body region is `(⟨ts.reverse⟩, .nat :: ts)` and returns a flag followed by the
  new state. A flag of `0` stops the loop (break). Regions capture nothing, so anything the
  body needs, including functions, must be passed in the state.
- **`funcs sigs ts rs`**: the regions are the main region `(⟨(fnTys sigs ++ ts).reverse⟩, rs)`
  followed by one body per signature `(n, m)`, of shape `(⟨(fnTys sigs ++ nats n).reverse⟩,
  nats m)`. Every region sees every function of the group as a value. The denotation is
  `(main (rev (fnVals (funcsFix fun T => bodies sigs T sigs regs) ++ xs))).map rev`.
- **`call n m`**: applies a function value to `n` numbers. A wrong number of results gives
  `none`.

## Key results

- **`Com.denote_mono`** (`Mono.lean`): every CF program is monotone. Values are ordered by
  how defined they are:
  - functions pointwise by `⊑` in `Option`;
  - numbers only below themselves.

  The relations are `ValLe`/`HVLe`/`VLe`/`OptLe`. The proof is a mutual structural
  recursion that mirrors the framework's `denote`. Per-op cases are in `denote_mono`. The
  `while` case uses `whileLoop_rel`, a fixpoint induction that works for any relation on
  loop states.
- **`bodies_monotone`**: if a group's bodies are monotone, the group is monotone in its table.
- **`funcsFix_bodies_unfold sigs regs`**: for any program, the table equals its bodies
  calling the table. This is the general reduction rule for mutual recursion, with no proof
  obligation left to the program.
- **`funcsFix_apply sigs rs hrs i xs`**: the table at any index `i`, unfolded once, for any
  regions `rs` with `RegsMono rs` (from `HVector.denote_mono` for a program). With
  `bodies_zero`/`bodies_succ` (or just `rfl` on a concrete group) it gives
  `T i xs = (ofNats n xs).bind fun ys => (bodyᵢ (fnVals T sigs ++ ys)).map toNats`.
- **`F'_eq`** (`MutualRec.lean`): `F' n = some (f n)`. The proof pattern:
  1. `fBody_denote` / `gBody_denote`: each body run on its arguments equals its equation.
     These use `cf_reduce`, `simp only [Option.bind_assoc, …]`, `cf_reduce`, then
     `simp only [Option.bind_map, Option.map_bind, …]` (to push the results' `.map rev`
     through), then a case split on `ofNats 1 r`.
  2. `T_f` / `T_g`: the fixpoint at index `i` on `[n]` runs body `i`, one line each:
     `(funcsFix_apply _ _ hFb i [n]).trans rfl`, where `hFb := HVector.denote_mono bodyRegs`.
  3. `table`: induction on `n`.
  4. `F'_eq`: `cf_reduce` reduces `prog`, then `erw` with `table`.
- **`Fib'_eq`** (`Loop.lean`): `Fib' n = some (fib n)`. The proof pattern:
  1. `step_eq`: the body as a step function (`step`), one case per branch, each by `rfl`.
  2. `loop`: induction on `n` with `whileLoop_unfold` and `step_eq`; the loop ends in state
     `(0, iter n a b, _)`.
  3. `Fib'_eq`: `cf_reduce` reduces `prog` up to the `whileLoop`, `erw [loop …]`, then
     `cf_reduce` again and `iter_fib`.
- **`Mul'_eq`** (`Nested.lean`): `Mul' n m = some (n * m)`. The proof pattern for nested loops:
  1. Step lemmas per loop, split into a zero and a successor case (`innerStep_zero`/`_succ`),
     each by `rfl`, except the outer successor step, which runs the inner loop:
     `cf_reduce`, `erw [inner_loop …]`, `rfl`.
  2. Each loop by `whileLoop_inv`, with the invariant and measure defined by pattern
     matching on the state vector (`innerInv`, `innerMeasure`): stating them with
     `st.head`/`st.tail.head` leaves `match` terms that `omega` cannot see through.
  3. `Mul'_eq`: `cf_reduce`, `erw [outer_loop …]`, `cf_reduce`, `simp`.
- **`Sumsq'_eq`** (`FuncLoop.lean`): a loop calling a function, inside a function.
  1. The loop is proved for *any* function value `fv` with `IsSq fv` (`∀ i, fv [i] = some
     [i * i]`): in `step_succ`, `cf_reduce` stops at the call `fv [i + 1]`, `rw [hf]`, `rfl`.
     The invariant also says the function in the state stays `fv`.
  2. `T_sq : IsSq (T 0)` by `funcsFix_apply` and `rfl`; `T_sumsq` by `funcsFix_apply`, then
     the body: `cf_reduce`, `erw [loop (T 0) T_sq n 0]`, `cf_reduce`, `simp`.
  3. `Sumsq'_eq`: `cf_reduce`, then `erw` with `T_sumsq` restated with `funcsFix` as its head.

## `cf_reduce` (Simp.lean)

`cf_reduce` rewrites the goal to a definitionally equal one. It reduces every data subterm
by unfolding its head while that makes progress, using `whnfCore` with
`unfoldDefinition?`/`unfoldProjInst?`. It is designed to stop at what is not known:

- it never unfolds into a `match` that is stuck (`isStuck`);
- it never unfolds `ite`/`dite`; `decideIte` picks a branch only when the condition
  decides;
- it never unfolds `funcsFix` or `whileLoop`;
- it leaves arithmetic and decision instances alone (`keptClass`, `isArith`);
- it skips function-typed, type, proof and instance subterms;
- it zeta-reduces at the end and runs at most 100 passes.

As a result, a call to an unknown function stays as `(gv [n]).bind …`, and the rest
evaluates. It is heuristic: it has been tested on the two examples only.

Pitfalls found along the way:
- Plain `simp` with the framework lemmas gets stuck on variable lookups. Literal `⟨i, h⟩`
  variables become `Var.last` over `Ctxt.ofList` contexts, which the framework lemmas do
  not match.
- `rfl` between two `Com.denote` terms can take forever. Normalize with `simp only` and
  `congr` first.
- `rw` of `(table n).1` fails because the abbrev `T` hides the `funcsFix` head. Restate it
  as `funcsFix Fb 0 [n] = …`.
- `cf_reduce` also reduces inside the `whileLoop`'s step function, so afterwards it no longer
  matches `step` syntactically: `rw [loop …]` fails, `erw` works.
- To build `RegsMono` for a concrete group, give the regions `HVector` its full type in a
  definition (`bodyRegs`). Writing `fBody ::ₕ gBody ::ₕ .nil` inline fails: unification
  cannot solve `?t.1 =?= ⟨[F, F, N]⟩`.
- Mutual theorems over `Com CF Γ .impure ty` are not structurally recursive, because the
  index is not a variable. Take `eff` with `heff : eff = .impure` instead, make the
  recursive calls before `subst heff`, and use `toOpt` for the result type.

## Remaining work

Finished: syntax, all four nestings (loop in loop, loop in function, call in loop, recursion),
termination (`whileLoop_inv`) and divergence (`whileLoop_diverges`) lemmas, `cf_simp`. Open:

1. **Generality (a redesign).** Values are only `nat` and `fn` over number lists. A reusable
   version would parameterize over a base dialect, as upstream's
   `SSA/Projects/Scf/ScfFunctor.lean` does (`Scf d` wraps a dialect `d` with `coe`, and
   `HasBool`/`HasInt` pick out its types). That `scf` uses the same region-op mechanism, but
   only for terminating loops (`iterate k`, `for` with a fixed count), with one value per
   region and no functions. Function values (`fn n m`) would need to range over the base
   dialect's types, so `toNats`/`ofNats`/`fnVals` and `Mono.lean`'s order generalize too.
2. **Proof ergonomics.** Every proof needs `erw` after `cf_reduce`, because `cf_reduce` also
   reduces inside loop and function bodies (so they no longer match `step`, `fBody`, …
   syntactically). A `cf_reduce` that leaves the arguments of `whileLoop`/`funcsFix` alone
   would make plain `rw` work. Step lemmas per loop are still written by hand.
3. **Syntax polish (optional).** Only MLIR's generic op syntax (`"cf.add"(%a, %b) : (…) ->
   (…)`) is supported; a custom short syntax (as for LLVM's `llvm.add %a, %b : i64`) would
   be macros onto the same AST. The framework's reversed result binding also means a
   multi-result op whose result types differ does not typecheck in syntax unless the
   dialect reverses its results, as CF does (worth reporting upstream).
4. **Upstreaming.** `Prod.foldToExpr` (bug fix) and `Op.mkRegions`/`Op.mkExprWithRegions`
   (generic region parsing) are independent of RegionCf and could go to `main` on their own.
5. Old BlockIR files from an earlier design exist in the repo but are unused; don't confuse
   them with this work.
