/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean

/-!
# The `block_eval` simp set

The reduction rules of `Block.eval`, in the role of the equation lemmas Lean generates
for a recursive definition: `simp only [block_eval]` steps a BlockIR program the way
`simp only [f]` steps a recursive function `f`.
-/

/-- Reduction rules for `Block.eval` (and `Block.fn`). -/
register_simp_attr block_eval
