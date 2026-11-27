# RegionCF handoff

Structured control flow (if, loops, mutually recursive functions) built entirely from
**region ops** in LeanMLIR's existing SSA framework (`Com`/`Expr`). There is no separate IR.
Loops and recursion are Lean functions defined as fixpoints in `Option`, where "no value"
means the program does not terminate.

Status: everything below builds with no errors or warnings. Nothing is committed yet: all of
`LeanMLIR/LeanMLIR/RegionCF/` is untracked on branch `blockir`.

## Build

```sh
cd LeanMLIR
timeout 600 lake build LeanMLIR.RegionCF.MutualRec      # builds every module below
timeout 300 lake env lean --memory=4096 --threads=2 SomeScratch.lean
```

Always cap Lean runs (memory, threads, `timeout`, heartbeats ≤ 1000000), because a runaway
`rfl` or `whnf` can freeze the machine. Run `lake build <module>` before `lake env lean` on a
file that imports a new module, or the `.olean` will be missing.

## Files

| File | What it is |
|---|---|
| `Fix.lean` | The fixpoints. `whileLoop` (via `partial_fixpoint`) and `whileLoop_unfold`. `FnTable := Nat → List Nat → Option (List Nat)`. `funcsFix F` is the least fixpoint, defined with `Lean.Order.fix` when `F` is monotone (a classical `if`) and `implemented_by` a `partial def` so programs still run. `funcsFix_unfold (h : monotone F)`. |
| `Dialect.lean` | The `CF` dialect, with monad `Option`. Types: `nat` and `fn n m` (denoted as `List Nat → Option (List Nat)`). Ops: `cst add sub mul eqz` (pure); `ite ts rs`, `while ts`, `funcs sigs ts rs`, `call n m` (impure). Helpers `toNats`, `ofNats`, `fnVals`, `bodies`. Simp lemmas `denote_*` and `effectKind_*`, one per op. |
| `Simp.lean` | Lookup lemmas for literal variable indices, and the **`cf_reduce`** tactic. |
| `Mono.lean` | **The general monotonicity theorem** and `funcsFix_bodies_unfold`. |
| `MutualRec.lean` | Worked example: `funcs { f; g } in f(n)`, proved equal to a Lean `mutual` definition. |

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
- **`F'_eq`** (`MutualRec.lean`): `F' n = some (f n)`. The proof pattern:
  1. `fBody_denote` / `gBody_denote`: each body run on its arguments equals its equation.
     These use `cf_reduce`, then `simp only [Option.bind_assoc, …]`, then a case split on
     `ofNats 1 r`.
  2. `Fb_f` / `Fb_g`: the table applied at index `i` to input `[n]` runs body `i`.
  3. `T_f` / `T_g`: the same equation for the fixpoint, via `funcsFix_unfold`, with
     `Fb_monotone` coming from the general theorem in one line.
  4. `table`: induction on `n`.
  5. `F'_eq`: `cf_reduce` reduces `prog`, then rewrite with `table`.

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
evaluates. It is heuristic: it has been tested on the mutual-recursion example only.

Pitfalls found along the way:
- Plain `simp` with the framework lemmas gets stuck on variable lookups. Literal `⟨i, h⟩`
  variables become `Var.last` over `Ctxt.ofList` contexts, which the framework lemmas do
  not match.
- `rfl` between two `Com.denote` terms can take forever. Normalize with `simp only` and
  `congr` first.
- `rw` of `(table n).1` fails because the abbrev `T` hides the `funcsFix` head. Restate it
  as `funcsFix Fb 0 [n] = …`.
- Mutual theorems over `Com CF Γ .impure ty` are not structurally recursive, because the
  index is not a variable. Take `eff` with `heff : eff = .impure` instead, make the
  recursive calls before `subst heff`, and use `toOpt` for the result type.

## Remaining work

1. **Loop example.** Write a `while` program (for example a counter or Fibonacci with a
   break flag, ideally with a nested loop exit) and prove it equals a Lean spec using
   `whileLoop_unfold` and `cf_reduce`. Nothing has exercised `while` in a proof yet.
2. **Generic per-function equation.** Write a lemma giving
   `funcsFix (bodies …) i xs = (ofNats n xs).bind (body i …)` for any group and any `i`.
   It would replace the per-program `Fb_f`/`Fb_g`/`T_f`/`T_g`.
3. **Harden `cf_reduce`.** Try it on larger and nested programs. Consider making it a
   `simp` pre-pass or `dsimproc`, and folding the `Option.bind_assoc` step in.
4. **Generality.** Values are only `nat` and `fn` over number lists. A reusable version
   would parameterize over a base dialect or value type.
5. **Commit.** Old BlockIR files from an earlier design exist in the repo but are unused;
   don't confuse them with this work.
