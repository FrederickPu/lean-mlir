import LeanMLIR.BlockIR.WellScoped
import LeanMLIR.BlockIR.Tests

open OpAlgebra BlockSSA BlockSSA.Tests

/-! `Block.WellScoped` on lowered and hand-written programs. -/

-- the lowered `scf.for` sum and `scf.if` programs are well scoped
#guard (sumTo.toProgram L).map (fun p => Block.wellScoped p.blocks) == some true
#guard (pick.toProgram L).map (fun p => Block.wellScoped p.blocks) == some true

/-- Block 1 reads `x`, which only its caller (block 0) binds. -/
def leaky : List (Block natAlg) :=
  [⟨[], [⟨["x"], .ofPrimOp (.const 1), []⟩, ⟨["y"], .call (.ofData 1), []⟩,
         ⟨[], .ret (.ofData 0), [.ofVar "y"]⟩]⟩,
   ⟨[], [⟨[], .ret (.ofData 1), [.ofVar "x"]⟩]⟩]

/-- Block 1 returns to block 0's label, unwinding past its caller. -/
def unwinding : List (Block natAlg) :=
  [⟨[], [⟨["y"], .call (.ofData 1), []⟩, ⟨[], .ret (.ofData 0), [.ofVar "y"]⟩]⟩,
   ⟨[], [⟨["k"], .ofPrimOp (.const 7), []⟩, ⟨[], .ret (.ofData 0), [.ofVar "k"]⟩]⟩]

#guard Block.wellScoped leaky == false
#guard Block.wellScoped unwinding == false

-- and it is a `Decidable` proposition
example : ¬ Block.WellScoped leaky := by decide
