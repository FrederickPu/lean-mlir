# RegionCF handoff

Structured control flow (if, loops, mutually recursive functions) built entirely from
**region ops** in LeanMLIR's existing SSA framework (`Com`/`Expr`). There is no separate IR.
Loops and recursion are Lean functions defined as fixpoints in `Option`, where "no value"
means the program does not terminate.

Status: everything below builds with no errors, warnings or `sorry`, on branch `blockir`.

## Build

```sh
cd LeanMLIR
timeout 600 lake build LeanMLIR.RegionCF.Loop      # builds every module below
timeout 300 lake env lean --memory=4096 --threads=2 SomeScratch.lean
```

Always cap Lean runs (memory, threads, `timeout`, heartbeats ≤ 1000000), because a runaway
`rfl` or `whnf` can freeze the machine. Run `lake build <module>` before `lake env lean` on a
file that imports a new module, or the `.olean` will be missing.

On a fresh checkout: no Mathlib binary cache exists for this nightly Mathlib revision
(`lake exe cache get` finds nothing), so the first build compiles ~670 modules from source.
If lake fails with `git exited with code 128` on a package, `git fetch origin <rev>` inside
`.lake/packages/<pkg>` and check out the pinned revision by hand.

## Files

| File | What it is |
|---|---|
| `Fix.lean` | The fixpoints. `whileLoop` (via `partial_fixpoint`) and `whileLoop_unfold`. `FnTable := Nat → List Nat → Option (List Nat)`. `funcsFix F` is the least fixpoint, defined with `Lean.Order.fix` when `F` is monotone (a classical `if`) and `implemented_by` a `partial def` so programs still run. `funcsFix_unfold (h : monotone F)`. |
| `Dialect.lean` | The `CF` dialect, with monad `Option`. Types: `nat` and `fn n m` (denoted as `List Nat → Option (List Nat)`). Ops: `cst add sub mul eqz` (pure); `ite ts rs`, `while ts`, `funcs sigs ts rs`, `call n m` (impure). Helpers `toNats`, `ofNats`, `fnVals`, `bodies`. Simp lemmas `denote_*` and `effectKind_*`, one per op. |
| `Simp.lean` | Lookup lemmas for literal variable indices, and the **`cf_reduce`** tactic. |
| `Mono.lean` | **The general monotonicity theorem**, `funcsFix_bodies_unfold`, and the per-function equation `funcsFix_apply` with simp lemmas `bodies_zero`/`bodies_succ`, `ofNats_*`, `toNats_*`, `fnVals_*`. |
| `MutualRec.lean` | Worked example: `funcs { f; g } in f(n)`, proved equal to a Lean `mutual` definition. |
| `Loop.lean` | Worked example: Fibonacci as a `while` whose body is an `ite` (continue, or break with flag `0`), proved equal to a Lean `fib`. |

## Semantics of the region ops

- **`ite ts rs`**: the first argument is the condition (nonzero means true), and the other
  arguments `ts` go to whichever branch runs. Each branch region is `(⟨ts⟩, rs)`.
- **`while ts`**: the body region is `(⟨ts⟩, .nat :: ts)` and returns a flag followed by the
  new state. A flag of `0` stops the loop (break). Regions capture nothing, so anything the
  body needs, including functions, must be passed in the state.
- **`funcs sigs ts rs`**: the regions are the main region `(⟨fnTys sigs ++ ts⟩, rs)` followed
  by one body per signature `(n, m)`, of shape `(⟨fnTys sigs ++ nats n⟩, nats m)`. Every
  region sees every function of the group as a value. The denotation is
  `main (fnVals (funcsFix fun T => bodies sigs T sigs regs) ++ xs)`.
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
     These use `cf_reduce`, then `simp only [Option.bind_assoc, …]`, then a case split on
     `ofNats 1 r`.
  2. `T_f` / `T_g`: the fixpoint at index `i` on `[n]` runs body `i`, one line each:
     `(funcsFix_apply _ _ hFb i [n]).trans rfl`, where `hFb := HVector.denote_mono bodyRegs`.
  3. `table`: induction on `n`.
  4. `F'_eq`: `cf_reduce` reduces `prog`, then rewrite with `table`.
- **`Fib'_eq`** (`Loop.lean`): `Fib' n = some (fib n)`. The proof pattern:
  1. `step_eq`: the body as a step function (`step`), one case per branch, each by `rfl`.
  2. `loop`: induction on `n` with `whileLoop_unfold` and `step_eq`; the loop ends in state
     `(0, iter n a b, _)`.
  3. `Fib'_eq`: `cf_reduce` reduces `prog` up to the `whileLoop`, `erw [loop …]`, then
     `cf_reduce` again and `iter_fib`.

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

1. **Nested loops.** `Loop.lean` has a single loop. Not yet tried: a loop nested in a loop,
   a loop inside a `funcs` body, or a `call` inside a loop body (functions must be threaded
   through the state).
2. **Generic loop lemma.** `loop` is proved by hand. A reusable lemma could state:
   if a step relation is an invariant and a measure decreases, then `whileLoop` ends in a
   state satisfying the invariant with flag `0`.
3. **Harden `cf_reduce`.** Try it on larger and nested programs. Consider making it a
   `simp` pre-pass or `dsimproc`, and folding the `Option.bind_assoc` step in.
4. **Generality.** Values are only `nat` and `fn` over number lists. A reusable version
   would parameterize over a base dialect or value type.
5. Old BlockIR files from an earlier design exist in the repo but are unused; don't confuse
   them with this work.
