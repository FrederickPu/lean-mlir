/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework.Basic
import LeanMLIR.BlockIR.BlockSSA
import LeanMLIR.BlockIR.Lemmas

/-!
# ShallowSSA → BlockSSA → BlockIR, with a correctness proof

Any LeanMLIR dialect `d` lowers to BlockIR through BlockSSA. The lowered program
is completely untyped:

* **Data** is the dialect's "any" type `Σ t : d.Ty, ⟦t⟧`. Block labels are values
  of a dialect type chosen by `DialectLabels`.
* **PrimOp** is just `d.Op`. Region-free ops are evaluated with `DialectDenote`.
* **Regions** become BlockIR blocks. An op with regions is not a primop: the dialect
  lowers it to block-level control flow with `RegionOps` (e.g. `scf.if` becomes a
  label `select` followed by a `call`).
* **Effects**: the dialect monad `d.m` is run as explicit state by `DialectRun`.

`Com.toProgram_run` proves that, for a region-free `Com`, running the lowered program
on the unchanged `Block.eval` gives exactly `Com.denote`.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open OpAlgebra BlockIR BlockSSA

set_option linter.unusedSectionVars false

namespace BlockIR.Shallow

/-! ## What a dialect provides -/

/-- How to run the effects of dialect `d` as explicit state. -/
class DialectRun (d : Dialect) [Monad d.m] where
  State : Type
  run {α : Type} : d.m α → State → Option (α × State)
  run_pure {α : Type} (a : α) (s : State) : run (pure a) s = some (a, s)
  run_bind {α β : Type} (x : d.m α) (f : α → d.m β) (s : State) :
    run (x >>= f) s = (run x s).bind fun p => run (f p.1) p.2

instance {Op Ty : Type} : DialectRun ⟨Op, Ty, Id⟩ where
  State := Unit
  run x s := some (x.run, s)
  run_pure _ _ := rfl
  run_bind _ _ _ := rfl

instance {Op Ty σ : Type} : DialectRun ⟨Op, Ty, StateM σ⟩ where
  State := σ
  run x s := some (x.run s)
  run_pure _ _ := rfl
  run_bind _ _ _ := rfl

/-- Which dialect type holds block labels (e.g. an index or pointer type). -/
class DialectLabels (d : Dialect) [TyDenote d.Ty] where
  labelTy : d.Ty
  toIdx : ⟦labelTy⟧ → Nat
  ofIdx : Nat → ⟦labelTy⟧
  toIdx_ofIdx (i : Nat) : toIdx (ofIdx i) = i

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DecidableEq d.Ty] [Monad d.m] [LawfulMonad d.m] [DialectRun d] [DialectLabels d]

/-! ## The operator algebra of a dialect -/

variable (d) in
/-- Untyped runtime values: the dialect's "any" type. -/
abbrev Data : Type := Σ t : d.Ty, ⟦t⟧

def encode : {ts : List d.Ty} → HVector toType ts → List (Data d)
  | [], .nil => []
  | t :: _, .cons x xs => ⟨t, x⟩ :: encode xs

@[simp] theorem encode_nil : encode (d := d) (ts := []) .nil = [] := rfl
@[simp] theorem encode_cons (x : ⟦t⟧) (xs : HVector toType ts) :
    encode (d := d) (.cons x xs) = ⟨t, x⟩ :: encode xs := rfl


def decode : (ts : List d.Ty) → List (Data d) → Option (HVector toType ts)
  | [], [] => some .nil
  | t :: ts, ⟨t', x⟩ :: ds =>
    if h : t' = t then (decode ts ds).map (.cons (h ▸ x)) else none
  | _, _ => none

/-- The (only) region argument vector of an op without regions. -/
def noRegions {F : _ → Type} {l : RegionSignature d.Ty} (h : l = []) : HVector F l :=
  h ▸ HVector.nil

/-- A label as a value. -/
def ofLabel (i : Nat) : Data d := ⟨DialectLabels.labelTy, DialectLabels.ofIdx i⟩

/-- Read a value as a label. -/
def toLabel? : Data d → Option Nat
  | ⟨t, x⟩ => if h : t = DialectLabels.labelTy then some (DialectLabels.toIdx (h ▸ x)) else none

variable (d) in
/-- The BlockIR operator algebra of dialect `d`. Ops with regions have no primop
semantics; they must be lowered to blocks (`RegionOps`). -/
abbrev alg : OpAlgebra where
  PrimOp := d.Op
  Data := Data d
  State := DialectRun.State d
  eval op s inputs :=
    if h : DialectSignature.regSig op = [] then do
      let args ← decode _ inputs
      let (r, s') ← DialectRun.run (d := d)
        (EffectKind.liftEffect (EffectKind.le_impure _)
          (DialectDenote.denote op args (noRegions h))) s
      return (encode r, s')
    else none
  novalue := ofLabel 0
  toBlockIdx? := toLabel?
  ofBlockIdx := ofLabel

/-! ## Lowering `Com` to BlockSSA -/

/-- The register for de Bruijn *level* `k` (levels never change as contexts grow). -/
def nm (k : Nat) : String := String.ofList (List.replicate (k + 1) 'v')

def varName (Γ : Ctxt d.Ty) (v : Γ.Var t) : String := nm (Γ.length - 1 - v.val)

def varNames (Γ : Ctxt d.Ty) : {ts : List d.Ty} → HVector Γ.Var ts → List String
  | [], .nil => []
  | _ :: _, .cons v vs => varName Γ v :: varNames Γ vs

/-- Registers for the variables of `Γ`, in index order. -/
def ctxtNames (Γ : Ctxt d.Ty) : List String :=
  (List.range Γ.length).map fun i => nm (Γ.length - 1 - i)

/-- Registers for the results `ty` bound on top of `Γ`. -/
def resultNames (Γ : Ctxt d.Ty) (ty : List d.Ty) : List String :=
  (List.range ty.length).map fun j => nm (ty.length + Γ.length - 1 - j)

mutual
/-- The statements and returned registers of a `Com`. -/
def comStmts : {Γ : Ctxt d.Ty} → {eff : EffectKind} → {ty : List d.Ty} →
    Com d Γ eff ty → List (Stmt d.Op) × List String
  | Γ, _, _, .rets vs => ([], varNames Γ vs)
  | _, _, _, .var e body => (exprStmt e :: (comStmts body).1, (comStmts body).2)

/-- `results = op(args) { regions }`, with the regions translated too. -/
def exprStmt : {Γ : Ctxt d.Ty} → {eff : EffectKind} → {t : List d.Ty} →
    Expr d Γ eff t → Stmt d.Op
  | Γ, _, t, .mk op _ _ args regs => .mk (resultNames Γ t) op (varNames Γ args) (regionsStmts regs)

/-- Each region becomes an BlockSSA region over its own context. -/
def regionsStmts : {l : RegionSignature d.Ty} →
    HVector (fun t : Ctxt d.Ty × List d.Ty => Com d t.1 .impure t.2) l → List (Region d.Op)
  | [], .nil => []
  | ⟨Γr, _⟩ :: _, .cons c cs =>
    .mk (ctxtNames Γr) (comStmts c).1 (comStmts c).2 :: regionsStmts cs
end

@[simp] theorem comStmts_rets (vs : HVector Γ.Var ty) :
    comStmts (Com.rets (d := d) (eff := eff) vs) = ([], varNames Γ vs) := by
  simp [comStmts]

@[simp] theorem comStmts_var (e : Expr d Γ eff t) (body : Com d e.outContext eff ty) :
    comStmts (Com.var e body) = (exprStmt e :: (comStmts body).1, (comStmts body).2) := by
  simp [comStmts]

def _root_.Com.toRegion (c : Com d Γ eff ty) : Region d.Op :=
  .mk (ctxtNames Γ) (comStmts c).1 (comStmts c).2

variable (d) in
/-- How a dialect lowers its ops *with regions* to BlockIR control flow, given the
blocks the regions were lowered to. -/
structure RegionOps where
  lowerOp : d.Op → (results args : List String) → (regionBlocks : List Nat) →
    BuilderM (alg d) (List (alg d).Instruction)

/-- No op with regions can be lowered. -/
def RegionOps.none : RegionOps d := ⟨fun _ _ _ _ => failure⟩

/-- Region-free ops are primops; ops with regions go to `R`. -/
def lowering (R : RegionOps d) : Lowering d.Op (alg d) where
  lowerOp op results args regions :=
    if regions.isEmpty then pure [⟨results, .ofPrimOp op, vars args⟩]
    else R.lowerOp op results args regions

/-- The BlockIR program of a `Com`. -/
def _root_.Com.toProgram (c : Com d Γ eff ty) (R : RegionOps d := .none) :
    Option (Program (alg d)) :=
  c.toRegion.toProgram (lowering R)

/-- The block arguments for a valuation, in index order. -/
def encodeVal {Γ : Ctxt d.Ty} (V : Valuation Γ) : List (Data d) :=
  (List.finRange Γ.length).map fun i =>
    ⟨Γ.toList.get i, V ⟨i, by simp [Ctxt.getElem?_eq_toList_getElem?]⟩⟩

/-- A `Com` whose ops have no regions. -/
def _root_.Com.RegionFree (c : Com d Γ eff ty) : Prop :=
  c.rec' (motive := fun _ => Prop) (fun _ => True)
    (fun e _ r => DialectSignature.regSig e.op = [] ∧ r)

/-! ## Correctness -/

section Proof
open EffectKind (liftEffect le_impure)

/-- The instruction a region-free statement lowers to. -/
def stmtInstr : Stmt d.Op → (alg d).Instruction
  | .mk r op a _ => ⟨r, .ofPrimOp op, vars a⟩

theorem hvector_nil_eq {F : _ → Type} {l : RegionSignature d.Ty} (h : l = [])
    (x y : HVector F l) : x = y := by
  subst h; cases x; cases y; rfl

theorem regionsStmts_of_nil {l : RegionSignature d.Ty} (h : l = [])
    (regs : HVector (fun t : Ctxt d.Ty × List d.Ty => Com d t.1 .impure t.2) l) :
    regionsStmts regs = [] := by
  subst h; cases regs; simp [regionsStmts]

theorem toLabel?_ofLabel (i : Nat) : toLabel? (ofLabel (d := d) i) = some i := by
  simp [toLabel?, ofLabel, DialectLabels.toIdx_ofIdx]

/-! ### Encoding -/

theorem decode_encode {ts : List d.Ty} (xs : HVector toType ts) :
    decode (d := d) ts (encode xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, decode, ih]

theorem length_encode {ts : List d.Ty} (xs : HVector toType ts) :
    (encode (d := d) xs).length = ts.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [encode, ih]

theorem getElem?_encode {ts : List d.Ty} (xs : HVector toType ts) (v : Var ⟨ts⟩ t) :
    (encode (d := d) xs)[v.val]? = some ⟨t, xs[v]⟩ := by
  induction xs with
  | nil => exact v.emptyElim
  | cons x xs ih =>
    cases v using Var.casesOn with
    | toCons v => simpa [encode, Var.val_toCons] using ih v
    | last => simpa [encode, Var.val_last] using (HVector.cons_getElem_last (xs := xs) x).symm

/-! ### Effects -/

theorem lift_pure (a : α) :
    liftEffect (le_impure eff) (pure a : eff.toMonad d.m α) = (pure a : d.m α) := by
  cases eff <;> rfl

theorem lift_bind (x : eff.toMonad d.m α) (f : α → eff.toMonad d.m β) :
    liftEffect (le_impure eff) (x >>= f) =
      ((liftEffect (le_impure eff) x : d.m α) >>= fun a => liftEffect (le_impure eff) (f a)) := by
  cases eff
  · simp only [EffectKind.liftEffect_pure_impure, pure_bind]; rfl
  · rfl

theorem lift_lift {e₁ e₂ : EffectKind} (h : e₁ ≤ e₂) (x : e₁.toMonad d.m α) :
    liftEffect (le_impure e₂) (liftEffect h x) = liftEffect (le_impure e₁) x := by
  cases e₁ <;> cases e₂ <;> first | rfl | cases h

/-! ### Names and environments -/

theorem nm_inj {a b : Nat} : nm a = nm b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have := congrArg List.length (String.ofList_injective h)
  simpa using this

/-- `e` holds the (encoded) value of every variable of `Γ`, under its level name. -/
def Inv (Γ : Ctxt d.Ty) (V : Valuation Γ) (e : Std.HashMap String (Data d)) : Prop :=
  ∀ t (v : Γ.Var t), e[varName Γ v]? = some ⟨t, V v⟩

theorem mapM_vars {Γ : Ctxt d.Ty} {V : Valuation Γ} {e : Std.HashMap String (Data d)}
    (hInv : Inv Γ V e) {ts : List d.Ty} (vs : HVector Γ.Var ts) :
    (vars (opAlg := alg d) (varNames Γ vs)).mapM (·.instantiate e) = some (encode (vs.map V)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [varNames, vars, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]
    simp [Arg.instantiate, hInv _ v, encode, HVector.map]

theorem val_lt_length {Γ : Ctxt d.Ty} (v : Γ.Var t) : v.val < Γ.length := by
  have h := v.prop
  rw [Ctxt.getElem?_eq_toList_getElem?] at h
  exact (List.getElem?_eq_some_iff.1 h).1

theorem nodup_resultNames (Γ : Ctxt d.Ty) (u : List d.Ty) : (resultNames Γ u).Nodup := by
  refine List.nodup_range.map_on fun x hx y hy hxy => ?_
  simp only [List.mem_range] at hx hy
  have := nm_inj.1 hxy
  omega

theorem map_fst_zip_resultNames (Γ : Ctxt d.Ty) (r : HVector toType u) :
    ((resultNames Γ u).zip (encode (d := d) r)).map Prod.fst = resultNames Γ u :=
  List.map_fst_zip (by simp [resultNames, length_encode])

theorem zip?_resultNames (Γ : Ctxt d.Ty) {u : List d.Ty} (r : HVector toType u) :
    (resultNames Γ u).zip? (encode (d := d) r) = some ((resultNames Γ u).zip (encode r)) := by
  simp [List.zip?, resultNames, length_encode]

theorem Inv.extend {Γ : Ctxt d.Ty} {V : Valuation Γ} {e : Std.HashMap String (Data d)}
    (hInv : Inv Γ V e) {u : List d.Ty} (r : HVector toType u) :
    Inv (⟨u⟩ ++ Γ) (r ++ V) (bindPairs (opAlg := alg d) e ((resultNames Γ u).zip (encode r))) := by
  intro t v
  cases v using Var.appendCases with
  | left v =>
    have hlt := val_lt_length v
    rw [bindPairs_getElem?_of_mem (opAlg := alg d) (ps := (resultNames Γ u).zip (encode r))
      (by rw [map_fst_zip_resultNames]; exact nodup_resultNames Γ u)
      (v := (⟨t, r[v]⟩ : Data d))]
    · simp
    rw [List.mem_iff_getElem?]
    refine ⟨v.val, List.getElem?_zip_eq_some.2 ⟨?_, getElem?_encode r v⟩⟩
    simp only [Ctxt.length] at hlt
    simp [resultNames, varName, Var.appendInl, hlt, Ctxt.length]
  | right v =>
    have hlt := val_lt_length v
    have hname : varName (⟨u⟩ ++ Γ) v.appendInr = varName Γ v := by
      simp only [varName, Var.appendInr, Ctxt.length_append]
      congr 1; simp only [Ctxt.length] at *; omega
    rw [hname, bindPairs_getElem?_of_not_mem, hInv]
    · simp
    rw [map_fst_zip_resultNames]
    simp only [resultNames, varName, List.mem_map, List.mem_range, not_exists, not_and]
    intro j hj h
    have := nm_inj.1 h
    simp only [Ctxt.length] at *
    omega

theorem Inv.init (Γ : Ctxt d.Ty) (V : Valuation Γ) :
    Inv Γ V (bindPairs (opAlg := alg d) ∅ ((ctxtNames Γ).zip (encodeVal V))) := by
  have hnd : (ctxtNames Γ).Nodup := by
    refine List.nodup_range.map_on fun x hx y hy hxy => ?_
    simp only [List.mem_range] at hx hy
    have := nm_inj.1 hxy
    simp only [Ctxt.length] at *
    omega
  intro t v
  have hlt := val_lt_length v
  rcases v with ⟨i, hi⟩
  have hi' := hi
  rw [Ctxt.getElem?_eq_toList_getElem?] at hi'
  obtain ⟨hlt', heq⟩ := List.getElem?_eq_some_iff.1 hi'
  subst heq
  rw [bindPairs_getElem?_of_mem (opAlg := alg d) (ps := (ctxtNames Γ).zip (encodeVal V))
    (by rw [List.map_fst_zip (by simp [ctxtNames, encodeVal])]; exact hnd)
    (v := (⟨_, V ⟨i, hi⟩⟩ : Data d))]
  rw [List.mem_iff_getElem?]
  refine ⟨i, List.getElem?_zip_eq_some.2 ⟨?_, ?_⟩⟩
  · simp [ctxtNames, varName, hlt]
  · simp only [encodeVal, List.getElem?_map]
    rw [List.getElem?_eq_getElem (by simpa [Ctxt.length] using hlt')]
    simp only [Option.map_some]
    have hx : ((List.finRange Γ.length)[i]'(by simpa [Ctxt.length] using hlt')).val = i := by simp
    generalize (List.finRange Γ.length)[i]'_ = x at hx ⊢
    obtain ⟨xv, xp⟩ := x
    simp only at hx
    subst hx
    rfl


/-! ### The lowering -/

theorem lowerOp_nil (R : RegionOps d) (op : d.Op) (r a : List String) :
    (lowering R).lowerOp op r a [] = (pure [⟨r, .ofPrimOp op, vars a⟩] : BuilderM (alg d) _) :=
  rfl

theorem lowerAll_comStmts (R : RegionOps d) (c : Com d Γ eff ty) (hc : c.RegionFree)
    (st : BuilderState (alg d)) :
    Stmt.lowerAll (lowering R) (comStmts c).1 st = some ((comStmts c).1.map stmtInstr, st) := by
  induction c generalizing st with
  | rets vs => simp [Stmt.lowerAll]; rfl
  | var e body ih =>
    obtain ⟨he, hb⟩ := hc
    rcases e with ⟨op, rfl, heff, args, regs⟩
    simp only [comStmts_var, Stmt.lowerAll, Stmt.lower, exprStmt,
      regionsStmts_of_nil he regs, Region.lowerAll]
    rw [pure_bind, lowerOp_nil, pure_bind]
    simp [bind, StateT.bind, ih hb, pure, StateT.pure, stmtInstr]

/-! ### Running the lowered block -/

theorem straight_comStmts (c : Com d Γ eff ty) (hc : c.RegionFree) (V : Valuation Γ)
    (e : Std.HashMap String (Data d)) (hInv : Inv Γ V e) (s : DialectRun.State d)
    (cs : List Nat) :
    straight (opAlg := alg d) cs e s
        ((comStmts c).1.map stmtInstr ++ [⟨[], .ret (label 0), vars (comStmts c).2⟩]) =
      (DialectRun.run (d := d) (liftEffect (le_impure eff) (c.denote V)) s).map
        fun p => ⟨cs.dropFromLast 0, encode p.1, p.2⟩ := by
  induction c generalizing e s with
  | rets vs =>
    simp only [Com.denote_rets, lift_pure, DialectRun.run_pure]
    simp only [comStmts_rets, List.map_nil, List.nil_append, straight]
    rw [mapM_vars hInv]
    simp [label, Arg.instantiate, toLabel?_ofLabel]
  | var e' body ih =>
    obtain ⟨he, hb⟩ := hc
    rcases e' with ⟨op, rfl, heff, args, regs⟩
    simp only [Expr.op] at he
    simp only [comStmts_var, List.map_cons, List.cons_append, exprStmt, stmtInstr, straight]
    rw [mapM_vars hInv]
    simp only [Option.bind_some, Com.denote_var, lift_bind, DialectRun.run_bind, Expr.denote]
    simp only [lift_lift, lift_pure, DialectRun.run_pure, Valuation.cast_rfl, decode_encode,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, dif_pos he]
    try simp only [Expr.op, Expr.args, Expr.regArgs]
    rw [hvector_nil_eq he (HVector.denote regs) (noRegions he)]
    rcases hr : DialectRun.run (d := d) (liftEffect (le_impure _)
      (DialectDenote.denote op (HVector.map V args) (noRegions he))) s with _ | ⟨r, s'⟩
    · simp only [hr, Option.bind_none, Option.map_none]
    simp only [hr, Option.bind_some, zip?_resultNames]
    exact ih hb (r ++ V) _ (hInv.extend r) s'

/-! ### The whole program -/

/-- The lowered block of a region-free `Com`. -/
def comBlock (c : Com d Γ eff ty) : Block (alg d) :=
  ⟨ctxtNames Γ, (comStmts c).1.map stmtInstr ++ [⟨[], .ret (label 0), vars (comStmts c).2⟩]⟩

theorem toProgram_eq (R : RegionOps d) (c : Com d Γ eff ty) (hc : c.RegionFree) :
    c.toProgram R = some ⟨[comBlock c], 0⟩ := by
  simp [Com.toProgram, Region.toProgram, BuilderM.toProgram, Com.toRegion, Region.lower,
    BuilderM.newBlock, BuilderM.setBlock, bind, StateT.bind, StateT.run, modifyGet,
    MonadStateOf.modifyGet, StateT.modifyGet, modify, lowerAll_comStmts R c hc,
    pure, StateT.pure, comBlock]

theorem noCall_comBlock (c : Com d Γ eff ty) : NoCall (comBlock c).instructions := by
  intro i hi t
  simp only [comBlock, List.mem_append, List.mem_map, List.mem_singleton] at hi
  rcases hi with ⟨⟨r, p, a, regs⟩, _, rfl⟩ | rfl <;> simp [stmtInstr]

end Proof

/-- **Correctness**: lowering a region-free `Com` to BlockIR (through BlockSSA) and
running it on the trusted `Block.eval` gives exactly the shallow denotation `Com.denote`. -/
theorem _root_.Com.toProgram_run (R : RegionOps d) (c : Com d Γ eff ty) (hc : c.RegionFree)
    (V : Valuation Γ) (s : DialectRun.State d) :
    ((c.toProgram R).bind fun p => p.run s (encodeVal V)) =
      (DialectRun.run (d := d) (EffectKind.liftEffect (EffectKind.le_impure eff) (c.denote V)) s).map
        fun p => (encode p.1, p.2) := by
  have hzip : (ctxtNames Γ).zip? (encodeVal V) = some ((ctxtNames Γ).zip (encodeVal V)) := by
    simp [List.zip?, ctxtNames, encodeVal]
  rw [toProgram_eq R c hc]
  simp only [Option.bind_some, Program.run, List.getElem?_cons_zero, Option.pure_def,
    Option.bind_eq_bind]
  rw [Block.eval_of_noCall _ _ _ _ _ _ (noCall_comBlock c)]
  simp only [comBlock] at hzip ⊢
  rw [hzip, Option.bind_some, straight_comStmts c hc V _ (Inv.init Γ V)]
  cases DialectRun.run (d := d) (EffectKind.liftEffect (EffectKind.le_impure eff) (c.denote V)) s <;>
    simp

end BlockIR.Shallow
