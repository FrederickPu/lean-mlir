/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Tactic
import LeanMLIR.BlockIR.Steps

/-!
# `@[block_program]`: the well-scopedness gate for a BlockIR program

Tagging a program `P` with `@[block_program]` proves `P.wellScoped` (by kernel `decide`) and
adds `P.call := Block.step_call P P.wellScoped` to `block_eval`: in `P`, a call becomes
`Block.fn P j args s`, a function value that is unfolded only on request
(`Block.fn_step P j`). This is the only program-specific rule; everything between calls is
reduced by the generic `block_eval` simp set.

Surface IRs prove their own reduction rules from the same two pieces: the gate (for their
lowered programs) and `block_eval`.
-/

open Lean Meta Elab

namespace BlockIR.ProgramGen

/-- Prove `P.wellScoped` by kernel `decide` and register `P.call`. -/
def genProgram (P : Name) : MetaM Unit := do
  let pc := mkConst P
  let ty ← mkAppM ``OpAlgebra.Block.WellScoped #[pc]
  let pf ← Term.TermElabM.run' do
    let e ← Term.elabTermEnsuringType (← `(by decide +kernel)) (some ty)
    Term.synthesizeSyntheticMVarsNoPostponing
    instantiateMVars e
  let wsName := P ++ `wellScoped
  addDecl (.thmDecl { name := wsName, levelParams := [], type := ty, value := pf })
  let callPf ← mkAppM ``OpAlgebra.Block.step_call #[pc, mkConst wsName]
  let callName := P ++ `call
  addDecl (.thmDecl { name := callName, levelParams := [], type := ← inferType callPf,
                      value := callPf })
  let some ext ← getSimpExtension? `block_eval | throwError "block_program: no `block_eval`"
  addSimpTheorem ext callName (post := true) (inv := false) .global (prio := 1100)

initialize registerBuiltinAttribute {
  name := `block_program
  descr := "prove a BlockIR program well scoped and make its calls fold to `Block.fn`"
  add := fun decl _ _ => (genProgram decl).run' }

end BlockIR.ProgramGen
