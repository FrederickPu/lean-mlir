/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.BlockSSA

/-!
# `scf.for` / `scf.if` as BlockIR abbreviations

Structured control flow is not primitive. It is defined as macro-expansions into
BlockIR blocks that use only `call`, `ret` and three primops supplied by the target
algebra: `lt`, `add`, and `select` (which picks one of two labels, using label
reflection). So it adds nothing to the trust base.

`for iv = lb to ub step s iter_args(inits) { body(iv, iters) -> yields }` expands to:
```
H(iv, ub, s, iters..):  c = lt(iv, ub); t = select(c, @S, @E)
                        r.. = call t(iv, ub, s, iters..); ret @H r..
S(iv, ub, s, iters..):  y.. = call @body(iv, iters..); iv' = add(iv, s)
                        r.. = call @H(iv', ub, s, y..); ret @S r..
E(iv, ub, s, iters..):  ret @E iters..
results = call @H(lb, ub, s, inits..)
```
-/

namespace BlockSSA
open OpAlgebra BlockIR BuilderM

variable {opAlg : OpAlgebra}

/-- The primops the expansions need from the target algebra. -/
structure ScfPrims (opAlg : OpAlgebra) where
  lt : opAlg.PrimOp
  add : opAlg.PrimOp
  /-- `select(c, a, b)`: `a` if `c` is true, else `b` (used on labels). -/
  select : opAlg.PrimOp

/-- Expand an `scf.for` whose body was lowered to block `body`.
  `args = lb :: ub :: step :: inits`. -/
def lowerFor (P : ScfPrims opAlg) (body : Nat) (results args : List String) :
    BuilderM opAlg (List opAlg.Instruction) := do
  let (lb, ub, st, inits) ← match args with
    | lb :: ub :: st :: inits => pure (lb, ub, st, inits)
    | _ => failure
  let n := inits.length
  let iv ← fresh "iv"; let ubN ← fresh "ub"; let stN ← fresh "step"
  let iters ← freshN "iter" n
  let params := iv :: ubN :: stN :: iters
  let c ← fresh "cond"; let tgt ← fresh "tgt"; let rH ← freshN "r" n
  let ys ← freshN "y" n; let iv' ← fresh "iv"; let rS ← freshN "r" n
  let hdr ← newBlock
  let step ← newBlock
  let exit ← newBlock
  setBlock exit ⟨params, [⟨[], .ret (label exit), vars iters⟩]⟩
  setBlock step ⟨params, [
    ⟨ys, .call (label body), vars (iv :: iters)⟩,
    ⟨[iv'], .ofPrimOp P.add, vars [iv, stN]⟩,
    ⟨rS, .call (label hdr), vars (iv' :: ubN :: stN :: ys)⟩,
    ⟨[], .ret (label step), vars rS⟩]⟩
  setBlock hdr ⟨params, [
    ⟨[c], .ofPrimOp P.lt, vars [iv, ubN]⟩,
    ⟨[tgt], .ofPrimOp P.select, [.ofVar c, label step, label exit]⟩,
    ⟨rH, .call (.ofVar tgt), vars params⟩,
    ⟨[], .ret (label hdr), vars rH⟩]⟩
  return [⟨results, .call (label hdr), vars (lb :: ub :: st :: inits)⟩]

/-- Expand an `scf.if c { then } else { else }`. -/
def lowerIf (P : ScfPrims opAlg) (thenB elseB : Nat) (results args : List String) :
    BuilderM opAlg (List opAlg.Instruction) := do
  let c ← match args with | [c] => pure c | _ => failure
  let tgt ← fresh "tgt"
  return [⟨[tgt], .ofPrimOp P.select, [.ofVar c, label thenB, label elseB]⟩,
          ⟨results, .call (.ofVar tgt), []⟩]

/-- An op of a dialect extended with structured control flow. -/
inductive ScfOp (Ω : Type) where
  | for_ | if_
  | base (op : Ω)

/-- Lower `ScfOp Ω`, delegating base ops to `L`. -/
def Lowering.withScf (P : ScfPrims opAlg) (L : Lowering Ω opAlg) :
    Lowering (ScfOp Ω) opAlg where
  lowerOp
    | .for_, rs, as, [body] => lowerFor P body rs as
    | .if_, rs, as, [t, e] => lowerIf P t e rs as
    | .base op, rs, as, regs => L.lowerOp op rs as regs
    | _, _, _, _ => failure

end BlockSSA
