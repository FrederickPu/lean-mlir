import LeanMLIR.BlockIR.Tactic
import LeanMLIR.BlockIR.ShallowTests

open BlockIR.ShallowTests

/-- `simp_ssa` reduces the denotation of typed SSA to plain Lean: here the stretch
`x = 2; y = x + x` (as a `Lets`), whose result `y` is `4`. The dialect's op
semantics are passed explicitly since this test dialect tags none `@[simp_denote]`. -/
example : twice.denote Ctxt.Valuation.nil (v 0 (Γ := ⟨[.nat, .nat]⟩)) = (4 : Nat) := by
  simp_ssa [twice, cst, add, v, DialectDenote.denote]
