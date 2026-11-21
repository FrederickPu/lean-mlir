/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Core

/-!
# BlockIR builder

A small monad for emitting BlockIR programs: allocate blocks, fill them in, and
generate fresh register names. Used by every lowering into BlockIR; not trusted.
-/

namespace BlockIR
open OpAlgebra

structure BuilderState (opAlg : OpAlgebra) where
  blocks : Array (Block opAlg) := #[]
  fresh : Nat := 0

/-- Emitting BlockIR. Fails (`none`) on malformed input. -/
abbrev BuilderM (opAlg : OpAlgebra) := StateT (BuilderState opAlg) Option

namespace BuilderM
variable {opAlg : OpAlgebra}

/-- A fresh register name `%pfx.n`. -/
def fresh (pfx : String) : BuilderM opAlg String :=
  modifyGet fun s => (s!"%{pfx}.{s.fresh}", { s with fresh := s.fresh + 1 })

/-- `n` fresh register names. -/
def freshN (pfx : String) (n : Nat) : BuilderM opAlg (List String) :=
  (List.range n).mapM fun _ => fresh pfx

/-- Allocate an (empty) block and return its index. Fill it with `setBlock`.
  Allocating before filling lets a block refer to its own label, or to blocks
  that refer back to it (loops). -/
def newBlock : BuilderM opAlg Nat :=
  modifyGet fun s => (s.blocks.size, { s with blocks := s.blocks.push ⟨[], []⟩ })

def setBlock (i : Nat) (b : Block opAlg) : BuilderM opAlg Unit :=
  modify fun s => { s with blocks := s.blocks.set! i b }

/-- Run a builder whose result is the entry block. -/
def toProgram (m : BuilderM opAlg Nat) : Option (Program opAlg) := do
  let (entry, s) ← m.run {}
  return ⟨s.blocks.toList, entry⟩

end BuilderM

/-- The static label of block `i`, as an instruction argument. -/
def label {opAlg : OpAlgebra} (i : Nat) : opAlg.Arg := .ofData (opAlg.ofBlockIdx i)

/-- Registers as instruction arguments. -/
def vars {opAlg : OpAlgebra} (xs : List String) : List opAlg.Arg := xs.map .ofVar

end BlockIR
