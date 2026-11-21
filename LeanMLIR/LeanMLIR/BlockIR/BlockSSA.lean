/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Builder

/-!
# Block SSA

The middle layer: ShallowSSA (typed `Com`) → **BlockSSA** → BlockIR.

This file has exactly three parts:
1. **Syntax** — `Stmt` and `Region`: untyped, named SSA with nested regions.
   There are no types; a dialect with dependent types (Mojo, Rust MIR, ...) encodes
   types as `Data` and checks them in its primops.
2. **`Lowering`** — what a dialect supplies: how one op becomes BlockIR instructions,
   given the blocks its regions were lowered to.
3. **`Region.toProgram`** — the translation. Each region becomes one block that ends
   in `ret` to its own label.

BlockSSA has no semantics of its own: `Region.run` *is* lowering + `Program.run`.
-/

namespace BlockSSA
open OpAlgebra BlockIR

/-! ## 1. Syntax -/

mutual
/-- `results = op(args) { regions }` -/
inductive Stmt (Ω : Type) where
  | mk (results : List String) (op : Ω) (args : List String) (regions : List (Region Ω))

/-- `^(args): body; yield rets` -/
inductive Region (Ω : Type) where
  | mk (args : List String) (body : List (Stmt Ω)) (rets : List String)
end

/-! ## 2. The dialect interface -/

/-- How a dialect lowers one op `results = op(args) { regions }`, where `regionBlocks`
  are the block indices its regions were lowered to. -/
structure Lowering (Ω : Type) (opAlg : OpAlgebra) where
  lowerOp : (op : Ω) → (results args : List String) → (regionBlocks : List Nat) →
    BuilderM opAlg (List opAlg.Instruction)

/-- The default: every op is a primop, and ops with regions are rejected. -/
def Lowering.primOps {opAlg : OpAlgebra} (toPrim : Ω → Option opAlg.PrimOp) :
    Lowering Ω opAlg where
  lowerOp op results args regions := do
    unless regions.isEmpty do failure
    return [⟨results, .ofPrimOp (← toPrim op), vars args⟩]

/-! ## 3. The translation -/

variable {opAlg : OpAlgebra} (L : Lowering Ω opAlg)

mutual
def Stmt.lower : Stmt Ω → BuilderM opAlg (List opAlg.Instruction)
  | .mk results op args regions => do
    L.lowerOp op results args (← Region.lowerAll regions)

def Stmt.lowerAll : List (Stmt Ω) → BuilderM opAlg (List opAlg.Instruction)
  | [] => return []
  | s :: ss => return (← s.lower) ++ (← Stmt.lowerAll ss)

/-- Lower a region to a fresh block ending in `ret @self rets`; returns its index. -/
def Region.lower : Region Ω → BuilderM opAlg Nat
  | .mk args body rets => do
    let i ← BuilderM.newBlock
    let instrs ← Stmt.lowerAll body
    BuilderM.setBlock i ⟨args, instrs ++ [⟨[], .ret (label i), vars rets⟩]⟩
    return i

def Region.lowerAll : List (Region Ω) → BuilderM opAlg (List Nat)
  | [] => return []
  | r :: rs => return (← r.lower) :: (← Region.lowerAll rs)
end

/-- A top-level region as a BlockIR program, entered at that region's block. -/
def Region.toProgram (r : Region Ω) : Option (Program opAlg) :=
  BuilderM.toProgram (r.lower L)

/-- The semantics of BlockSSA, *defined* as lowering followed by `Program.run`. -/
def Region.run (r : Region Ω) (state : opAlg.State) (args : List opAlg.Data) :
    Option (List opAlg.Data × opAlg.State) := do
  (← r.toProgram L).run state args

end BlockSSA
