import LeanMLIR.BlockIR.Child
import LeanMLIR.BlockIR.Tests

open OpAlgebra BlockSSA BlockSSA.Tests

/-! `Block.childDec` on small programs (labels are `Nat`s in `natAlg`). -/

/-- Block 0 calls 1; block 1 calls 2; block 2 returns to block 0's label. -/
def deepReturn : List (Block natAlg) :=
  [⟨[], [⟨["y"], .call (.ofData 1), []⟩, ⟨[], .ret (.ofData 0), [.ofVar "y"]⟩]⟩,
   ⟨[], [⟨["z"], .call (.ofData 2), []⟩, ⟨[], .ret (.ofData 1), [.ofVar "z"]⟩]⟩,
   ⟨[], [⟨["k"], .ofPrimOp (.const 7), []⟩, ⟨[], .ret (.ofData 0), [.ofVar "k"]⟩]⟩]

-- block 2 returns to 0, so it unwinds past its caller 1: not a child of 1 ...
#guard Block.childDec deepReturn 1 2 == false
-- ... but called from 0 it returns to 0 itself, which goes through 0: a child of 0
#guard Block.childDec deepReturn 0 2 == true
-- block 1, called from 0, can only end by returning to 1 or (via 2) to 0
#guard Block.childDec deepReturn 0 1 == true

-- the lowered `scf.for` loop: the loop blocks are children of the function block
#guard (sumTo.toProgram L).map (fun p => Block.childDec p.blocks p.entry 1) == some true

-- the decision is a proof
example : Block.Child deepReturn 0 2 := Block.child_of_childDec _ _ _ (by native_decide)
