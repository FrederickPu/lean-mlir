import LeanMLIR.BlockIR.Scf

namespace BlockSSA.Tests
open OpAlgebra

inductive NatOp | lt | add | select | const (n : Nat)

abbrev natAlg : OpAlgebra where
  PrimOp := NatOp
  Data := Nat
  State := Unit
  eval
    | .lt, s, [a, b] => some ([if a < b then 1 else 0], s)
    | .add, s, [a, b] => some ([a + b], s)
    | .select, s, [c, a, b] => some ([if c != 0 then a else b], s)
    | .const n, s, [] => some ([n], s)
    | _, _, _ => none
  novalue := 0
  toBlockIdx? := some
  ofBlockIdx := id

def L : Lowering (ScfOp NatOp) natAlg :=
  (Lowering.primOps (opAlg := natAlg) some).withScf ⟨NatOp.lt, NatOp.add, NatOp.select⟩

/-- `sum = for i = 0 to n step 1 iter(acc = 0) { yield acc + i }` -/
def sumTo : Region (ScfOp NatOp) :=
  .mk ["n"] [
    .mk ["zero"] (.base (.const 0)) [] [],
    .mk ["one"] (.base (.const 1)) [] [],
    .mk ["sum"] .for_ ["zero", "n", "one", "zero"] [
      .mk ["i", "acc"] [.mk ["acc2"] (.base .add) ["acc", "i"] []] ["acc2"]]
  ] ["sum"]

/-- `if c then 10 else 20` -/
def pick : Region (ScfOp NatOp) :=
  .mk ["c"] [
    .mk ["r"] .if_ ["c"] [
      .mk [] [.mk ["x"] (.base (.const 10)) [] []] ["x"],
      .mk [] [.mk ["y"] (.base (.const 20)) [] []] ["y"]]
  ] ["r"]

#guard ((sumTo.run L () [(5 : Nat)]).map (·.1) : Option (List Nat)) == some [10]
#guard ((sumTo.run L () [(0 : Nat)]).map (·.1) : Option (List Nat)) == some [0]
#guard ((pick.run L () [(1 : Nat)]).map (·.1) : Option (List Nat)) == some [10]
#guard ((pick.run L () [(0 : Nat)]).map (·.1) : Option (List Nat)) == some [20]

end BlockSSA.Tests
