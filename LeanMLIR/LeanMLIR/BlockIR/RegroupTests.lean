import LeanMLIR.BlockIR.ShallowTests

/-!
# What regrouping produces

Untyped BlockIR instructions in, typed SSA out. Each `#guard` shows the reconstructed
`Lets` (one line per op: result registers, result types, op and argument registers),
followed by the typed context it ends in (newest variable first).

The dialect is `Cnt` from `ShallowTests`: `cst n`, `add`, and the effectful `tick`,
over a single type `nat`.
-/

open OpAlgebra BlockIR BlockIR.Shallow BlockIR.Regroup BlockIR.ShallowTests

namespace BlockIR.RegroupTests

/-- Short names for printing. -/
local instance : Repr Ty := ⟨fun _ _ => "nat"⟩
local instance : Repr Op := ⟨fun op _ => match op with
  | .cst n => s!"cst {n}" | .add => "add" | .tick => "tick" | .sel => "sel" | .ifz => "ifz"⟩

abbrev I := OpAlgebra.Instruction (alg Cnt)

def prim (rs : List String) (op : Op) (as : List String) : I := ⟨rs, .ofPrimOp op, as.map .ofVar⟩

/-- Regroup `stretch`, starting from variables of types `Γ` in registers `ns`. -/
def regroup (Γ : List Ty) (ns : List String) (stretch : List I) : Option (List String) :=
  (reconstruct (d := Cnt) ⟨Γ⟩ ns stretch).map (Acc.pretty (d := Cnt))

/-! ## Straight-line code becomes typed SSA -/

/-- `x = cst 2; y = add x x` -/
def ex1 : List I := [prim ["x"] (.cst 2) [], prim ["y"] .add ["x", "x"]]

#guard regroup [] [] ex1 == some
  ["[x] : [nat] := cst 2()",
   "[y] : [nat] := add(x, x)",
   "context: [(y, nat), (x, nat)]"]

/-- Using block arguments `a`, `b`, and an effectful op in the middle. -/
def ex2 : List I := [prim ["s"] .add ["a", "b"], prim ["t"] .tick [], prim ["u"] .add ["s", "t"]]

#guard regroup [.nat, .nat] ["a", "b"] ex2 == some
  ["[s] : [nat] := add(a, b)",
   "[t] : [nat] := tick()",
   "[u] : [nat] := add(s, t)",
   "context: [(u, nat), (t, nat), (s, nat), (a, nat), (b, nat)]"]

/-! ## A block with control flow splits into stretches -/

/-- `x = cst 1; y = add x x; r = call @3(y); z = add r y; ret @0 z` -/
def ex3 : List I :=
  [prim ["x"] (.cst 1) [], prim ["y"] .add ["x", "x"],
   ⟨["r"], .call (label 3), [.ofVar "y"]⟩,
   prim ["z"] .add ["r", "y"],
   ⟨[], .ret (label 0), [.ofVar "z"]⟩]

#guard splitShape (d := Cnt) ex3 == ["stretch(2)", "call", "stretch(1)", "ret"]

-- the first stretch, from no variables:
#guard regroup [] [] (ex3.take 2) == some
  ["[x] : [nat] := cst 1()",
   "[y] : [nat] := add(x, x)",
   "context: [(y, nat), (x, nat)]"]

-- the stretch after the call, from `y`, `x` and the call's result `r`:
#guard regroup [.nat, .nat, .nat] ["r", "y", "x"] (ex3.drop 3 |>.take 1) == some
  ["[z] : [nat] := add(r, y)",
   "context: [(z, nat), (r, nat), (y, nat), (x, nat)]"]

/-! ## What does not regroup -/

-- an argument register that is not in scope
#guard regroup [] [] [prim ["y"] .add ["x", "x"]] == none
-- a register bound twice (not SSA)
#guard regroup [] [] [prim ["x"] (.cst 1) [], prim ["x"] (.cst 2) []] == none
-- too few arguments for `add`
#guard regroup [] [] [prim ["x"] (.cst 1) [], prim ["y"] .add ["x"]] == none
-- the wrong number of result registers
#guard regroup [] [] [prim ["x", "w"] (.cst 1) []] == none
-- an op with regions (it must be lowered to blocks, not regrouped)
#guard regroup [.nat] ["c"] [prim ["r"] .ifz ["c"]] == none
-- control flow is not part of a stretch
#guard regroup [] [] [⟨[], .ret (label 0), []⟩] == none

end BlockIR.RegroupTests
