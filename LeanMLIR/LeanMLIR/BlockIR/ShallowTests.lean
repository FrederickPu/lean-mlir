import LeanMLIR.BlockIR.Regroup

/-!
Running typed LeanMLIR programs through ShallowSSA → BlockSSA → BlockIR:
a pure program, an effectful one (`StateM Nat`), and one with an op with regions
(`ifz`) that is lowered to real blocks.
-/

open BlockIR.Shallow BlockIR
open Ctxt (Var)

namespace BlockIR.ShallowTests

inductive Ty | nat deriving DecidableEq, Repr
inductive Op | cst (n : Nat) | add | tick | sel | ifz deriving Repr

instance : TyDenote Ty where toType | .nat => Nat

/-- `tick` reads and increments a counter; `ifz c {then} {else}` has two regions. -/
abbrev Cnt : Dialect := ⟨Op, Ty, StateM Nat⟩

instance : DialectSignature Cnt where
  signature
    | .cst _ => ⟨[], [], [.nat], .pure⟩
    | .add => ⟨[.nat, .nat], [], [.nat], .pure⟩
    | .tick => ⟨[], [], [.nat], .impure⟩
    | .sel => ⟨[.nat, .nat, .nat], [], [.nat], .pure⟩
    | .ifz => ⟨[.nat], [(⟨[]⟩, [.nat]), (⟨[]⟩, [.nat])], [.nat], .impure⟩

instance : DialectDenote Cnt where
  denote
    | .cst n, _, _ => (.cons n .nil : HVector toType [Ty.nat])
    | .add, .cons (a : Nat) (.cons (b : Nat) .nil), _ => (.cons (a + b) .nil : HVector toType [Ty.nat])
    | .tick, _, _ => (do let n ← get; set (n + 1); return .cons n .nil : StateM Nat _)
    | .sel, .cons (c : Nat) (.cons (a : Nat) (.cons (b : Nat) .nil)), _ =>
      (.cons (if c = 0 then a else b) .nil : HVector toType [Ty.nat])
    | .ifz, .cons (c : Nat) .nil, .cons t (.cons e .nil) =>
      if c = 0 then t Ctxt.Valuation.nil else e Ctxt.Valuation.nil

/-- Labels are `nat` values. -/
instance : DialectLabels Cnt where
  labelTy := .nat
  toIdx n := n
  ofIdx n := n
  toIdx_ofIdx _ := rfl

/-- `ifz` lowers to `t = sel(c, @then, @else); results = call t()`. -/
def ifzLowering : RegionOps Cnt where
  lowerOp
    | .ifz, rs, [c], [thn, els] => do
      let tgt ← BuilderM.fresh "tgt"
      return [⟨[tgt], .ofPrimOp .sel, [.ofVar c, label thn, label els]⟩,
              ⟨rs, .call (.ofVar tgt), []⟩]
    | _, _, _, _ => failure

def v (i : Nat) {Γ : Ctxt Ty} (h : Γ[i]? = some .nat := by rfl) : Γ.Var .nat := ⟨i, h⟩

def cst (n : Nat) : Expr Cnt Γ eff [.nat] :=
  ⟨.cst n, rfl, EffectKind.pure_le _, .nil, .nil⟩
def add (a b : Γ.Var .nat) : Expr Cnt Γ eff [.nat] :=
  ⟨.add, rfl, EffectKind.pure_le _, .cons a (.cons b .nil), .nil⟩
def tick : Expr Cnt Γ .impure [.nat] :=
  ⟨.tick, rfl, le_refl _, .nil, .nil⟩
def ifz (c : Γ.Var .nat) (thn els : Com Cnt ⟨[]⟩ .impure [.nat]) : Expr Cnt Γ .impure [.nat] :=
  ⟨.ifz, rfl, le_refl _, .cons c .nil, .cons thn (.cons els .nil)⟩

/-- `x = 2; y = x + x; z = y + x; return z` -/
def pureProg : Com Cnt ⟨[]⟩ .pure [.nat] :=
  .var (cst 2) <| .var (add (v 0) (v 0)) <| .var (add (v 0) (v 1)) <| .rets (.cons (v 0) .nil)

/-- `a = tick; b = tick; c = a + b; return c` -/
def tickProg : Com Cnt ⟨[]⟩ .impure [.nat] :=
  .var tick <| .var tick <| .var (add (v 0) (v 1)) <| .rets (.cons (v 0) .nil)

/-- `return arg0 + arg1` -/
def argProg : Com Cnt ⟨[.nat, .nat]⟩ .pure [.nat] :=
  .var (add (v 0) (v 1)) <| .rets (.cons (v 0) .nil)

/-- `r = ifz arg0 { tick } { 100 }; return r` -/
def ifzProg : Com Cnt ⟨[.nat]⟩ .impure [.nat] :=
  .var (ifz (v 0) (.var tick <| .rets (.cons (v 0) .nil)) (.var (cst 100) <| .rets (.cons (v 0) .nil))) <|
  .rets (.cons (v 0) .nil)

def nat' (n : Nat) : Data Cnt := ⟨.nat, (n : Nat)⟩

def natResult? : Option (List (Data Cnt) × Nat) → Option (Nat × Nat)
  | some ([⟨.nat, x⟩], s) => some (x, s)
  | _ => none

-- pure: 2 + 2 + 2 = 6, counter untouched
#guard natResult? ((pureProg.toProgram).bind fun p => p.run (10 : Nat) []) == some (6, 10)
-- impure: ticks read 10 and 11, so 21; counter ends at 12
#guard natResult? ((tickProg.toProgram).bind fun p => p.run (10 : Nat) []) == some (21, 12)
-- block arguments: 3 + 4
#guard natResult? ((argProg.toProgram).bind fun p => p.run (0 : Nat) [nat' 3, nat' 4]) == some (7, 0)

-- regions as blocks: `ifz` takes the `tick` branch on 0, the constant branch otherwise
#guard natResult? ((ifzProg.toProgram ifzLowering).bind fun p => p.run (5 : Nat) [nat' 0]) == some (5, 6)
#guard natResult? ((ifzProg.toProgram ifzLowering).bind fun p => p.run (5 : Nat) [nat' 1]) == some (100, 5)
-- ... and it agrees with the shallow semantics
#guard ((ifzProg.denote (Ctxt.Valuation.ofHVector (.cons (0 : Nat) .nil))).run 5).2 == 6
-- without a lowering for `ifz`, the program does not lower at all
#guard (ifzProg.toProgram).isNone

-- the theorem applies to the region-free programs:
example (s : Nat) : ((tickProg.toProgram).bind fun p => p.run s (encodeVal (d := Cnt) Ctxt.Valuation.nil)) =
    (DialectRun.run (d := Cnt) (tickProg.denote Ctxt.Valuation.nil) s).map
      fun p => (encode (d := Cnt) p.1, p.2) :=
  Com.toProgram_run (d := Cnt) .none tickProg ⟨rfl, rfl, rfl, trivial⟩ _ s


/-! ## Proving things about a BlockIR program via the shallow embedding -/


section Reflection
open OpAlgebra BlockIR.Reflect

/-- The straight-line part `x = 2; y = x + x`, as typed SSA. -/
def twice : Lets Cnt ⟨[]⟩ .pure ⟨[.nat, .nat]⟩ :=
  .var (.var .nil (cst 2)) (add (v 0) (v 0))

/-- A hand-written BlockIR block with user-chosen register names `x`, `y`:
the straight-line part, then a `ret`. -/
def blk : Block (alg Cnt) :=
  ⟨[], twice.instrs ["y", "x"] ++ [⟨[], .ret (label 0), [.ofVar "y"]⟩]⟩

/-- Its result is proved by replacing the straight-line part with `Lets.denote`
(`Block.eval_lets`), then reading `y` out of the resulting environment. -/
example (s : Nat) : Block.eval [blk] s ∅ [0] blk [] = some ⟨[], [nat' 4], s⟩ := by
  obtain ⟨e', hN, heq⟩ := Block.eval_lets (d := Cnt) [blk] [0] twice ⟨rfl, rfl, trivial⟩
    ["y", "x"] rfl (by decide) Ctxt.Valuation.nil ∅ ⟨rfl, fun _ v => v.emptyElim⟩
    [⟨[], .ret (label 0), [.ofVar "y"]⟩] (s := s) rfl
  change Block.eval [blk] s ∅ [0] ⟨[], twice.instrs ["y", "x"] ++ _⟩ [] = _
  rw [heq]
  have hy := hN.2 _ (v 0 (Γ := ⟨[.nat, .nat]⟩))
  rw [Block.eval_of_noCall _ _ _ _ _ _ (by intro i hi t; simp at hi; subst hi; simp)]
  simp [straight, Arg.instantiate, label, toLabel?_ofLabel, List.zip?, bindPairs]
  have hval : twice.denote Ctxt.Valuation.nil (v 0 (Γ := ⟨[.nat, .nat]⟩)) = (4 : Nat) := rfl
  have hy' : e'["y"]? = some (nat' 4) := by
    rw [← hval]; exact hy
  rw [hy']
  rfl

end Reflection


/-! ## Regrouping an untyped block automatically -/

section Regrouping
open OpAlgebra BlockIR.Reflect BlockIR.Regroup

/-- Untyped instructions, as a parser or the lowering would produce them. -/
def rawStretch : List (alg Cnt).Instruction :=
  [⟨["x"], .ofPrimOp (.cst 2), []⟩,
   ⟨["y"], .ofPrimOp .add, [.ofVar "x", .ofVar "x"]⟩]

def rawBlock : List (alg Cnt).Instruction :=
  rawStretch ++ [⟨[], .ret (label 0), [.ofVar "y"]⟩]

-- the block splits into one stretch and the `ret`
#guard (splitStretches rawBlock).length == 2
-- the stretch reconstructs to typed SSA ...
#guard (reconstruct (d := Cnt) ⟨[]⟩ [] rawStretch).isSome
-- ... but not with an unknown register, a rebinding, or the wrong arity
#guard (reconstruct (d := Cnt) ⟨[]⟩ [] [⟨["y"], .ofPrimOp Op.add, [.ofVar "x", .ofVar "x"]⟩]).isNone
#guard (reconstruct (d := Cnt) ⟨[]⟩ [] [⟨["x"], .ofPrimOp (Op.cst 1), []⟩, ⟨["x"], .ofPrimOp (Op.cst 2), []⟩]).isNone
#guard (reconstruct (d := Cnt) ⟨[]⟩ [] [⟨["x"], .ofPrimOp Op.add, [.ofVar "x"]⟩]).isNone

/-- The reconstructed typed SSA (computed, not written by hand). -/
def rawAcc : Acc Cnt ⟨[]⟩ := (reconstruct ⟨[]⟩ [] rawStretch).get (by decide)

theorem rawAcc_spec : reconstruct ⟨[]⟩ [] rawStretch = some rawAcc := by simp [rawAcc]

/-- Running the untyped stretch is the shallow semantics of the reconstructed SSA. -/
example (s : Nat) : ∃ V' e', NInv rawAcc.Γ rawAcc.ns V' e' ∧
    Block.eval [⟨[], rawBlock⟩] s ∅ [0] ⟨[], rawStretch ++ [⟨[], .ret (label 0), [.ofVar "y"]⟩]⟩ [] =
      Block.eval [⟨[], rawBlock⟩] s e' [0] ⟨[], [⟨[], .ret (label 0), [.ofVar "y"]⟩]⟩ [] := by
  obtain ⟨e', h1, h2⟩ := Block.eval_regroup (d := Cnt) [⟨[], rawBlock⟩] [0] rawAcc_spec
    List.nodup_nil (V := Ctxt.Valuation.nil) (e := ∅) ⟨rfl, fun _ v => v.emptyElim⟩
    (rest := [⟨[], .ret (label 0), [.ofVar "y"]⟩]) (s := s) (s' := s) rfl
  exact ⟨_, e', h1, h2⟩

end Regrouping

end BlockIR.ShallowTests
