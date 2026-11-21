/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
-- The trusted core: only `Core.lean` defines semantics.
import LeanMLIR.BlockIR.Core
-- Untrusted: lowerings into the core, and proofs about it.
import LeanMLIR.BlockIR.Builder
import LeanMLIR.BlockIR.BlockSSA
import LeanMLIR.BlockIR.Scf
import LeanMLIR.BlockIR.Lemmas
import LeanMLIR.BlockIR.WellScoped
import LeanMLIR.BlockIR.Shallow
import LeanMLIR.BlockIR.Reflect
import LeanMLIR.BlockIR.Regroup
import LeanMLIR.BlockIR.Tactic
