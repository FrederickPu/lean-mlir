/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Shallow

/-!
# Reasoning about BlockIR programs with the shallow embedding

The lowering to BlockIR is fully untyped. To *prove* things about a practical
program, group its long call-free stretches back into ordinary typed SSA:

1. `Block.eval_append` (in `Lemmas`) splits a block at a call-free prefix.
2. If that prefix is `lets.instrs ns` — the instructions of a typed, region-free
   `Lets`, under register names `ns` that *you* choose — then `Block.eval_lets`
   replaces running it by `Lets.denote`, so the usual SSA machinery applies.
   Only `call`/`ret` control flow is left to reason about in BlockIR.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open OpAlgebra BlockIR BlockIR.Shallow
open EffectKind (liftEffect le_impure)

set_option linter.unusedSectionVars false

namespace BlockIR.Reflect

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DecidableEq d.Ty] [Monad d.m] [LawfulMonad d.m] [DialectRun d] [DialectLabels d]

/-! ## Typed straight-line code as BlockIR instructions -/

/-- The registers of variables, given the registers `ns` of their context (by index). -/
def argNames {Γ : Ctxt d.Ty} (ns : List String) : {ts : List d.Ty} → HVector Γ.Var ts → List String
  | [], .nil => []
  | _ :: _, .cons v vs => ns.getD v.val "" :: argNames ns vs

/-- A `Lets` whose ops have no regions. -/
def _root_.Lets.RegionFree : Lets d Γ_in eff Γ_out → Prop
  | .nil => True
  | .var body e => DialectSignature.regSig e.op = [] ∧ body.RegionFree

/-- The BlockIR instructions of a `Lets`, where `ns` names the variables of the
output context by index (newest first). -/
def _root_.Lets.instrs : Lets d Γ_in eff Γ_out → List String → List (alg d).Instruction
  | .nil, _ => []
  | .var (t := t) body e, ns =>
    body.instrs (ns.drop t.length) ++
      [⟨ns.take t.length, .ofPrimOp e.op, vars (argNames (ns.drop t.length) e.args)⟩]

/-- `e` holds the value of every variable of `Γ` under its register in `ns`. -/
def NInv (Γ : Ctxt d.Ty) (ns : List String) (V : Valuation Γ)
    (e : Std.HashMap String (Data d)) : Prop :=
  ns.length = Γ.length ∧ ∀ t (v : Γ.Var t), e[ns.getD v.val ""]? = some ⟨t, V v⟩

/-- How the shallow run of a `Lets` and the BlockIR run of its instructions agree. -/
def Agrees (Γ : Ctxt d.Ty) (ns : List String) :
    Option (Valuation Γ × DialectRun.State d) →
    Option ((alg d).BlockResult ⊕ (Std.HashMap String (Data d) × DialectRun.State d)) → Prop
  | none, none => True
  | some (V, s), some (.inr (e, s')) => s = s' ∧ NInv Γ ns V e
  | _, _ => False

/-! ## Proofs -/

theorem Lets.length_le (lets : Lets d Γ_in eff Γ_out) : Γ_in.length ≤ Γ_out.length := by
  induction lets with
  | nil => exact le_refl _
  | var body e ih => simp only [Expr.outContext, Ctxt.length_append] at *; omega

theorem mapM_argNames {Γ : Ctxt d.Ty} {ns : List String} {V : Valuation Γ}
    {e : Std.HashMap String (Data d)} (hInv : NInv Γ ns V e) {ts : List d.Ty}
    (vs : HVector Γ.Var ts) :
    (vars (opAlg := alg d) (argNames ns vs)).mapM (·.instantiate e) = some (encode (vs.map V)) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [argNames, vars, List.map_cons, List.mapM_cons] at ih ⊢
    rw [ih]
    have hv := hInv.2 _ v
    simp only [List.getD_eq_getElem?_getD] at hv
    simp [Arg.instantiate, hv, encode]

theorem NInv.extend {Γ : Ctxt d.Ty} {ns : List String} {V : Valuation Γ}
    {e : Std.HashMap String (Data d)} (hInv : NInv Γ ns V e) {u : List d.Ty}
    (r : HVector toType u) (rs : List String) (hlen : rs.length = u.length)
    (hnd : (rs ++ ns).Nodup) :
    NInv (⟨u⟩ ++ Γ) (rs ++ ns) (r ++ V) (bindPairs (opAlg := alg d) e (rs.zip (encode r))) := by
  have hfst : (rs.zip (encode (d := d) r)).map Prod.fst = rs :=
    List.map_fst_zip (by simp [hlen, length_encode])
  obtain ⟨hrs, hns, hdisj⟩ := List.nodup_append.1 hnd
  refine ⟨by simp [hlen, hInv.1, Ctxt.length], fun t v => ?_⟩
  cases v using Var.appendCases with
  | left v =>
    have hlt : v.val < rs.length := by
      have := val_lt_length v; simp only [Ctxt.length] at this; omega
    have hname : (rs ++ ns).getD (Var.appendInl v (Δ := Γ)).val "" = rs[v.val] := by
      simp [Var.appendInl, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt,
        List.getElem?_eq_getElem hlt]
    rw [hname, bindPairs_getElem?_of_mem (opAlg := alg d) (ps := rs.zip (encode r))
      (by rw [hfst]; exact hrs) (v := (⟨t, r[v]⟩ : Data d))]
    · simp
    rw [List.mem_iff_getElem?]
    exact ⟨v.val, List.getElem?_zip_eq_some.2 ⟨List.getElem?_eq_getElem hlt, getElem?_encode r v⟩⟩
  | right v =>
    have hlt : v.val < ns.length := by
      have := val_lt_length v; rw [hInv.1]; exact this
    have hname : (rs ++ ns).getD (Var.appendInr v (Γ := ⟨u⟩)).val "" = ns.getD v.val "" := by
      simp [Var.appendInr, List.getD_eq_getElem?_getD, Ctxt.length, ← hlen,
        List.getElem?_append_right, Nat.add_sub_cancel]
    rw [hname, bindPairs_getElem?_of_not_mem, hInv.2]
    · simp
    rw [hfst]
    intro hmem
    have hn : ns.getD v.val "" ∈ ns := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
    exact hdisj _ hmem _ hn rfl

theorem runPrefix_singleton (cs : List Nat) (e : Std.HashMap String (Data d))
    (s : DialectRun.State d) (i : (alg d).Instruction) :
    runPrefix cs e s [i] = runPrefix cs e s (i :: []) := rfl

/-- **Reflection**: the BlockIR instructions of a region-free `Lets` behave like its
shallow denotation `Lets.denote`. -/
theorem runPrefix_instrs (lets : Lets d Γ_in eff Γ_out) (hrf : lets.RegionFree)
    (cs : List Nat) (ns : List String) (hlen : ns.length = Γ_out.length) (hnd : ns.Nodup)
    (V : Valuation Γ_in) (e : Std.HashMap String (Data d))
    (hInv : NInv Γ_in (ns.drop (ns.length - Γ_in.length)) V e) (s : DialectRun.State d) :
    Agrees Γ_out ns
      (DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s)
      (runPrefix cs e s (lets.instrs ns)) := by
  induction lets generalizing ns s with
  | nil =>
    have : ns.drop (ns.length - Γ_in.length) = ns := by rw [hlen]; simp
    rw [this] at hInv
    simp only [Lets.denote, lift_pure, DialectRun.run_pure, Lets.instrs, runPrefix]
    exact (⟨rfl, hInv⟩ : s = s ∧ _)
  | @var Γb u body e' ih =>
    obtain ⟨he, hb⟩ := hrf
    rcases e' with ⟨op, rfl, heff, args, regs⟩
    simp only [Expr.op] at he
    have hbl := Lets.length_le body
    have hout : (Expr.outContext d (Expr.mk op rfl heff args regs)).length =
        (DialectSignature.returnTypes op).length + Γb.length := by
      simp [Expr.outContext, Ctxt.length]
    have hk : (DialectSignature.returnTypes op).length ≤ ns.length := by omega
    have hlen' : (ns.drop (DialectSignature.returnTypes op).length).length = Γb.length := by
      simp only [List.length_drop]; omega
    have hInv' : NInv Γ_in ((ns.drop (DialectSignature.returnTypes op).length).drop
        ((ns.drop (DialectSignature.returnTypes op).length).length - Γ_in.length)) V e := by
      have hns : ns.length = (DialectSignature.returnTypes op).length + Γb.length := by
        rw [hlen, hout]
      have hidx : (DialectSignature.returnTypes op).length +
          ((ns.drop (DialectSignature.returnTypes op).length).length - Γ_in.length) =
          ns.length - Γ_in.length := by
        simp only [List.length_drop]; simp only [Ctxt.length] at hbl hns ⊢; omega
      rw [List.drop_drop]
      first | rw [hidx]; exact hInv | rw [Nat.add_comm] at hidx; rw [hidx]; exact hInv
    have ihb := ih hb (ns.drop _) hlen' (hnd.sublist (List.drop_sublist _ _)) hInv' s
    simp only [Lets.instrs, runPrefix_append, Lets.denote, lift_bind, DialectRun.run_bind]
    cases h1 : DialectRun.run (d := d) (liftEffect (le_impure eff) (body.denote V)) s with
    | none =>
      rw [h1] at ihb
      cases h2 : runPrefix cs e s (body.instrs (ns.drop (DialectSignature.returnTypes op).length)) with
      | none => simp [Agrees]
      | some r => rw [h2] at ihb; cases r <;> simp [Agrees] at ihb
    | some p =>
      obtain ⟨W, s1⟩ := p
      rw [h1] at ihb
      cases h2 : runPrefix cs e s (body.instrs (ns.drop (DialectSignature.returnTypes op).length)) with
      | none => rw [h2] at ihb; simp [Agrees] at ihb
      | some r =>
        rw [h2] at ihb
        rcases r with r | ⟨e1, s1'⟩
        · simp [Agrees] at ihb
        obtain ⟨rfl, hW⟩ := ihb
        simp only [Option.bind_some]
        simp only [Expr.denote, map_eq_pure_bind, lift_bind,
          DialectRun.run_bind, lift_lift, lift_pure, DialectRun.run_pure, Valuation.cast_rfl,
          Option.pure_def, Option.bind_eq_bind, Option.bind_some, runPrefix, Expr.op, Expr.args,
          Expr.regArgs]
        rw [mapM_argNames hW]
        simp only [Option.bind_some, decode_encode, dif_pos he]
        rw [hvector_nil_eq he (HVector.denote regs) (noRegions he)]
        rcases DialectRun.run (d := d) (liftEffect (le_impure _)
          (DialectDenote.denote op (HVector.map W args) (noRegions he))) s1 with _ | ⟨r, s2⟩
        · simp [Agrees]
        have hzip : (ns.take (DialectSignature.returnTypes op).length).zip? (encode (d := d) r) =
            some ((ns.take (DialectSignature.returnTypes op).length).zip (encode r)) := by
          simp [List.zip?, length_encode, hk]
        simp only [Option.bind_some, hzip, Agrees, true_and]
        have := hW.extend r (ns.take (DialectSignature.returnTypes op).length) (by simp [hk])
          (by rw [List.take_append_drop]; exact hnd)
        rwa [List.take_append_drop] at this

theorem noCall_instrs (lets : Lets d Γ_in eff Γ_out) (ns : List String) :
    NoCall (lets.instrs ns) := by
  induction lets generalizing ns with
  | nil => intro i hi; simp [Lets.instrs] at hi
  | var body e ih =>
    intro i hi t
    simp only [Lets.instrs, List.mem_append, List.mem_singleton] at hi
    rcases hi with hi | rfl
    · exact ih _ i hi t
    · simp

/-- **Replace a straight-line stretch by its shallow semantics.** If a block begins
with the instructions of a region-free `Lets`, and the shallow run of that `Lets`
succeeds, then the block continues from an environment holding the `Lets`'s results. -/
theorem Block.eval_lets (blocks : List (Block (alg d))) (cs : List Nat)
    (lets : Lets d Γ_in eff Γ_out) (hrf : lets.RegionFree)
    (ns : List String) (hlen : ns.length = Γ_out.length) (hnd : ns.Nodup)
    (V : Valuation Γ_in) (e : Std.HashMap String (Data d))
    (hInv : NInv Γ_in (ns.drop (ns.length - Γ_in.length)) V e)
    (rest : List (alg d).Instruction) {s s' : DialectRun.State d} {V' : Valuation Γ_out}
    (hrun : DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s = some (V', s')) :
    ∃ e', NInv Γ_out ns V' e' ∧
      Block.eval blocks s e cs ⟨[], lets.instrs ns ++ rest⟩ [] =
        Block.eval blocks s' e' cs ⟨[], rest⟩ [] := by
  have hag := runPrefix_instrs lets hrf cs ns hlen hnd V e hInv s
  rw [hrun] at hag
  rw [Block.eval_append _ _ _ _ _ _ _ _ (noCall_instrs lets ns)]
  simp only [List.zip?, List.length_nil, beq_self_eq_true, if_true, List.zip_nil_left,
    Option.bind_some, bindPairs_nil]
  cases h : runPrefix cs e s (lets.instrs ns) with
  | none => rw [h] at hag; simp [Agrees] at hag
  | some r =>
    rw [h] at hag
    rcases r with r | ⟨e', s''⟩
    · simp [Agrees] at hag
    obtain ⟨rfl, hN⟩ := hag
    refine ⟨e', hN, ?_⟩
    rw [bindPairs_nil, h]
    rfl


/-! ## The environment after a stretch, explicitly

`envAfter e lets ns V'` is the environment the instructions of `lets` build from `e`,
given the values `V'` they compute: the same inserts, in the same order. Having it as a
term turns the reflection lemma into an *equation*, usable by `simp`. -/

/-- The variables `u` bound on top of `Γ`, read back out of a valuation, encoded. -/
def encPrefix {Γ : Ctxt d.Ty} (u : List d.Ty) (V : Valuation (⟨u⟩ ++ Γ)) : List (Data d) :=
  (List.finRange u.length).map fun i =>
    ⟨u.get i, V (Var.appendInl (Γ := ⟨u⟩) ⟨i.1, by simp [Ctxt.getElem?_eq_toList_getElem?]⟩)⟩

/-- The variables of `Γ` below `u`. -/
def vSuffix {Γ : Ctxt d.Ty} {u : List d.Ty} (V : Valuation (⟨u⟩ ++ Γ)) : Valuation Γ :=
  fun _ v => V (Var.appendInr v)

/-- The environment the instructions of `lets` build from `e`, given the values `V'`. -/
def envAfter (e : Std.HashMap String (Data d)) :
    Lets d Γ_in eff Γ_out → List String → Valuation Γ_out → Std.HashMap String (Data d)
  | .nil, _, _ => e
  | .var (t := t) body _, ns, V' =>
    bindPairs (opAlg := alg d) (envAfter e body (ns.drop t.length) (vSuffix (u := t) V'))
      ((ns.take t.length).zip (encPrefix t V'))

theorem vSuffix_append {Γ : Ctxt d.Ty} {u : List d.Ty} (r : HVector toType u) (W : Valuation Γ) :
    vSuffix (u := u) (r ++ W) = W := by
  funext t v; simp [vSuffix]

theorem encPrefix_append {Γ : Ctxt d.Ty} {u : List d.Ty} (r : HVector toType u) (W : Valuation Γ) :
    encPrefix (d := d) u (r ++ W) = encode r := by
  apply List.ext_getElem?
  intro i
  by_cases h : i < u.length
  · have hv : (⟨u⟩ : Ctxt d.Ty)[i]? = some (u.get ⟨i, h⟩) := by
      simp [Ctxt.getElem?_eq_toList_getElem?]
    rw [show i = (⟨i, hv⟩ : Var (⟨u⟩ : Ctxt d.Ty) (u.get ⟨i, h⟩)).val from rfl, getElem?_encode r]
    simp [encPrefix, h]
    have key : ∀ {t t' : d.Ty} (v : Var (⟨u⟩ : Ctxt d.Ty) t) (v' : Var (⟨u⟩ : Ctxt d.Ty) t'),
        v.val = v'.val → HEq r[v] r[v'] := by
      intro t t' v v' hvv
      have htt : t = t' := by
        have h1 := v.prop; have h2 := v'.prop
        rw [hvv] at h1; rw [h1] at h2; exact Option.some.inj h2
      subst htt
      have : v = v' := Subtype.ext hvv
      subst this; rfl
    exact key _ _ rfl
  · rw [List.getElem?_eq_none (by simpa [encPrefix] using h),
      List.getElem?_eq_none (by simpa [length_encode] using h)]

/-- **Reflection, as an equation**: running the instructions of a region-free `Lets`
is its shallow denotation, ending in the explicit environment `envAfter`. -/
theorem runPrefix_instrs_eq (lets : Lets d Γ_in eff Γ_out) (hrf : lets.RegionFree)
    (cs : List Nat) (ns : List String) (hlen : ns.length = Γ_out.length) (hnd : ns.Nodup)
    (V : Valuation Γ_in) (e : Std.HashMap String (Data d))
    (hInv : NInv Γ_in (ns.drop (ns.length - Γ_in.length)) V e) (s : DialectRun.State d) :
    runPrefix cs e s (lets.instrs ns) =
      (DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s).map
        fun p => .inr (envAfter e lets ns p.1, p.2) := by
  induction lets generalizing ns s with
  | nil =>
    simp only [Lets.denote, lift_pure, DialectRun.run_pure, Lets.instrs, runPrefix, envAfter,
      Option.map_some]
  | @var Γb u body e' ih =>
    obtain ⟨he, hb⟩ := hrf
    rcases e' with ⟨op, rfl, heff, args, regs⟩
    simp only [Expr.op] at he
    have hbl := Lets.length_le body
    have hout : (Expr.outContext d (Expr.mk op rfl heff args regs)).length =
        (DialectSignature.returnTypes op).length + Γb.length := by
      simp [Expr.outContext, Ctxt.length]
    have hk : (DialectSignature.returnTypes op).length ≤ ns.length := by omega
    have hlen' : (ns.drop (DialectSignature.returnTypes op).length).length = Γb.length := by
      simp only [List.length_drop]; omega
    have hnd' := hnd.sublist (List.drop_sublist (DialectSignature.returnTypes op).length ns)
    have hInv' : NInv Γ_in ((ns.drop (DialectSignature.returnTypes op).length).drop
        ((ns.drop (DialectSignature.returnTypes op).length).length - Γ_in.length)) V e := by
      have hns : ns.length = (DialectSignature.returnTypes op).length + Γb.length := by
        rw [hlen, hout]
      have hidx : (DialectSignature.returnTypes op).length +
          ((ns.drop (DialectSignature.returnTypes op).length).length - Γ_in.length) =
          ns.length - Γ_in.length := by
        simp only [List.length_drop]; simp only [Ctxt.length] at hbl hns ⊢; omega
      rw [List.drop_drop]
      first | rw [hidx]; exact hInv | rw [Nat.add_comm] at hidx; rw [hidx]; exact hInv
    have ihb := ih hb (ns.drop _) hlen' hnd' hInv' s
    have agb := runPrefix_instrs body hb cs _ hlen' hnd' V e hInv' s
    rw [ihb] at agb
    simp only [Lets.instrs, runPrefix_append, Lets.denote, lift_bind, DialectRun.run_bind, ihb]
    cases h1 : DialectRun.run (d := d) (liftEffect (le_impure eff) (body.denote V)) s with
    | none => simp
    | some p =>
      obtain ⟨W, s1⟩ := p
      rw [h1] at agb
      simp only [Option.map_some, Agrees, true_and] at agb
      simp only [Option.map_some, Option.bind_some]
      simp only [Expr.denote, map_eq_pure_bind, lift_bind,
        DialectRun.run_bind, lift_lift, lift_pure, DialectRun.run_pure, Valuation.cast_rfl,
        Option.pure_def, Option.bind_eq_bind, Option.bind_some, runPrefix, Expr.op, Expr.args,
        Expr.regArgs]
      rw [mapM_argNames agb]
      simp only [Option.bind_some, decode_encode, dif_pos he]
      rw [hvector_nil_eq he (HVector.denote regs) (noRegions he)]
      rcases DialectRun.run (d := d) (liftEffect (le_impure _)
        (DialectDenote.denote op (HVector.map W args) (noRegions he))) s1 with _ | ⟨r, s2⟩
      · simp
      have hzip : (ns.take (DialectSignature.returnTypes op).length).zip? (encode (d := d) r) =
          some ((ns.take (DialectSignature.returnTypes op).length).zip (encode r)) := by
        simp [List.zip?, length_encode, hk]
      simp only [Option.bind_some, hzip, Option.map_some, envAfter, vSuffix_append,
        encPrefix_append]


/-- **Step over a straight-line stretch**, as an equation: run its typed SSA with
`Lets.denote`, then continue in the explicit environment `envAfter`. -/
theorem Block.eval_lets_eq (blocks : List (Block (alg d))) (cs : List Nat)
    (lets : Lets d Γ_in eff Γ_out) (hrf : lets.RegionFree)
    (ns : List String) (hlen : ns.length = Γ_out.length) (hnd : ns.Nodup)
    (V : Valuation Γ_in) (e : Std.HashMap String (Data d))
    (hInv : NInv Γ_in (ns.drop (ns.length - Γ_in.length)) V e)
    (rest : List (alg d).Instruction) (s : DialectRun.State d) :
    Block.eval blocks s e cs ⟨[], lets.instrs ns ++ rest⟩ [] =
      (DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s).bind
        fun p => Block.eval blocks p.2 (envAfter e lets ns p.1) cs ⟨[], rest⟩ [] := by
  rw [Block.eval_append _ _ _ _ _ _ _ _ (noCall_instrs lets ns)]
  simp only [List.zip?, List.length_nil, beq_self_eq_true, if_true, List.zip_nil_left,
    Option.bind_some]
  rw [bindPairs_nil, runPrefix_instrs_eq lets hrf cs ns hlen hnd V e hInv s]
  cases DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s <;> rfl

/-- **Reading registers after a stretch**: `envAfter` holds every variable's value
under its register name. -/
theorem NInv.envAfter (lets : Lets d Γ_in eff Γ_out) (hrf : lets.RegionFree)
    (ns : List String) (hlen : ns.length = Γ_out.length) (hnd : ns.Nodup)
    (V : Valuation Γ_in) (e : Std.HashMap String (Data d))
    (hInv : NInv Γ_in (ns.drop (ns.length - Γ_in.length)) V e) {s s' : DialectRun.State d}
    {V' : Valuation Γ_out}
    (hrun : DialectRun.run (d := d) (liftEffect (le_impure eff) (lets.denote V)) s = some (V', s')) :
    NInv Γ_out ns V' (envAfter e lets ns V') := by
  have hag := runPrefix_instrs lets hrf [] ns hlen hnd V e hInv s
  rw [runPrefix_instrs_eq lets hrf [] ns hlen hnd V e hInv s, hrun] at hag
  exact hag.2

end BlockIR.Reflect
