import LeanMLIR.BlockIR.WellScoped
import LeanMLIR.BlockIR.Tactic

/-!
# Example: proving mutually recursive BlockIR functions correct

```
f 0 = 0      f (n+1) = 3·g n + (n+1)·(n+1) + 7
g 0 = 1      g (n+1) = 2·f n + (n+1) + 5
```

Each function is three untyped BlockIR blocks: a dispatcher that picks the base or
recursive block with a label `sel`ect, a base block, and a recursive block that does
arithmetic around a `call` to the other function.

The proof reasons about `call`/`ret` directly in BlockIR, but every straight-line
stretch (the arithmetic) is regrouped into typed SSA (`Block.eval_regroup`), so each
stretch is handled in one step by computing its `Lets.denote`, instead of stepping
through its instructions one at a time.
-/

open OpAlgebra BlockIR BlockIR.Shallow
open Ctxt (Var Valuation)
open TyDenote (toType)

namespace BlockIR.MutualRecExample

/-! ## The dialect: pure arithmetic on `Nat` -/

inductive Ty | nat deriving DecidableEq, Repr
inductive Op | cst (n : Nat) | add | sub | mul | iszero | sel deriving Repr

instance : TyDenote Ty where toType | .nat => Nat

abbrev Ar : Dialect := ⟨Op, Ty, Id⟩

instance : DialectSignature Ar where
  signature
    | .cst _ => ⟨[], [], [.nat], .pure⟩
    | .iszero => ⟨[.nat], [], [.nat], .pure⟩
    | .sel => ⟨[.nat, .nat, .nat], [], [.nat], .pure⟩
    | _ => ⟨[.nat, .nat], [], [.nat], .pure⟩

instance : DialectDenote Ar where
  denote
    | .cst n, _, _ => (.cons n .nil : HVector toType [Ty.nat])
    | .iszero, .cons (a : Nat) .nil, _ => (.cons ((if a = 0 then 1 else 0 : Nat)) .nil : HVector toType [Ty.nat])
    | .sel, .cons (c : Nat) (.cons (a : Nat) (.cons (b : Nat) .nil)), _ =>
      (.cons (if c ≠ 0 then a else b) .nil : HVector toType [Ty.nat])
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a + b) .nil : HVector toType [Ty.nat])
    | .sub, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a - b) .nil : HVector toType [Ty.nat])
    | .mul, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a * b) .nil : HVector toType [Ty.nat])

/-- Labels are `nat` values. -/
instance : DialectLabels Ar := ⟨.nat, id, id, fun _ => rfl⟩

/-! ## The specification -/

mutual
def f : Nat → Nat
  | 0 => 0
  | n + 1 => 3 * g n + (n + 1) * (n + 1) + 7
def g : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * f n + (n + 1) + 5
end

/-! ## The program: six untyped blocks -/

abbrev I := OpAlgebra.Instruction (alg Ar)
def prim (rs : List String) (op : Op) (as : List String) : I := ⟨rs, .ofPrimOp op, as.map .ofVar⟩
def nat' (n : Nat) : Data Ar := ⟨.nat, (n : Nat)⟩

/-- Dispatch on `n = 0`: `t = sel(iszero n, @base, @rec); r = call t(n); ret @self r`. -/
def dispatchStretch (base recur : Nat) : List I :=
  [prim ["z"] .iszero ["n"], prim ["lb"] (.cst base) [], prim ["lr"] (.cst recur) [],
   prim ["t"] .sel ["z", "lb", "lr"]]
def dispatch (self base recur : Nat) : Block (alg Ar) :=
  ⟨["n"], dispatchStretch base recur ++
    [⟨["r"], .call (.ofVar "t"), [.ofVar "n"]⟩, ⟨[], .ret (label self), [.ofVar "r"]⟩]⟩

/-- `return k` -/
def base (self k : Nat) : Block (alg Ar) :=
  ⟨["n"], [prim ["k"] (.cst k) [], ⟨[], .ret (label self), [.ofVar "k"]⟩]⟩

/-- `m = n - 1` -/
def predStretch : List I := [prim ["one"] (.cst 1) [], prim ["m"] .sub ["n", "one"]]

/-- `res = 3·a + n·n + 7` -/
def fStretch : List I :=
  [prim ["three"] (.cst 3) [], prim ["b"] .mul ["three", "a"], prim ["sq"] .mul ["n", "n"],
   prim ["c"] .add ["b", "sq"], prim ["seven"] (.cst 7) [], prim ["res"] .add ["c", "seven"]]

/-- `res = 2·a + n + 5` -/
def gStretch : List I :=
  [prim ["two"] (.cst 2) [], prim ["b"] .mul ["two", "a"], prim ["c"] .add ["b", "n"],
   prim ["five"] (.cst 5) [], prim ["res"] .add ["c", "five"]]

/-- `m = n - 1; a = call @other(m); res = ...; ret @self res` -/
def recBlock (self other : Nat) (body : List I) : Block (alg Ar) :=
  ⟨["n"], predStretch ++ ⟨["a"], .call (label other), [.ofVar "m"]⟩ :: (body ++
    [⟨[], .ret (label self), [.ofVar "res"]⟩])⟩

/-- Blocks: `0 = f`, `1 = f`'s base, `2 = f`'s recursion, `3 = g`, `4`, `5` likewise. -/
abbrev prog : List (Block (alg Ar)) :=
  [dispatch 0 1 2, base 1 0, recBlock 2 3 fStretch,
   dispatch 3 4 5, base 4 1, recBlock 5 0 gStretch]

def runF (n : Nat) : Option (List (Data Ar)) :=
  (Program.run ⟨prog, 0⟩ () [nat' n]).map (·.1)

def natOut : Option (List (Data Ar)) → Option Nat
  | some [⟨.nat, x⟩] => some x
  | _ => none

#guard (List.range 8).all fun n => natOut (runF n) == some (f n)

theorem prog_ws : Block.WellScoped prog := by decide

/-! ## Typed wrappers -/

def out1 : List (Data Ar) → Option Nat
  | [⟨.nat, x⟩] => some x
  | _ => none

/-- `f`, as computed by the BlockIR program. -/
def F (n : Nat) : Option Nat := (Block.fn prog 0 [nat' n] ()).bind fun r => out1 r.1
/-- `g`, as computed by the BlockIR program. -/
def G (n : Nat) : Option Nat := (Block.fn prog 3 [nat' n] ()).bind fun r => out1 r.1

set_option maxHeartbeats 400000 in
theorem F_zero : F 0 = some 0 := by
  block_unfold [F, nat', prim, out1] using prog_ws

set_option maxHeartbeats 400000 in
theorem G_zero : G 0 = some 1 := by
  block_unfold [G, nat', prim, out1] using prog_ws

set_option maxHeartbeats 1000000 in
theorem F_succ (n : Nat) : F (n + 1) = (G n).bind fun a => some (3 * a + (n + 1) * (n + 1) + 7) := by
  block_unfold [F, G, nat', prim, out1] using prog_ws
  trace_state
  sorry

end BlockIR.MutualRecExample
