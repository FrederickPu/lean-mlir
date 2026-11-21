/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.BlockIR.Reflect

/-!
# Regrouping untyped BlockIR into typed SSA

Takes an untyped BlockIR/BlockSSA block and recovers typed SSA for its straight-line
stretches, so they can be reasoned about with `Lets.denote` (see `Reflect`).

* `splitStretches` cuts an instruction list into maximal stretches of primops,
  separated by the `call`/`ret` instructions between them.
* `reconstruct Γ ns stretch` rebuilds a typed, region-free `Lets` from a stretch,
  given the types `Γ` and registers `ns` of the variables in scope. It infers types
  from `DialectSignature`, and fails on unknown registers, type mismatches, ops with
  regions, or a register bound twice.
* `reconstruct_sound` proves the result really is that stretch, so the reconstructor
  is not trusted.
* `Block.eval_regroup` replaces running a reconstructed stretch by `Lets.denote`.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open OpAlgebra BlockIR BlockIR.Shallow BlockIR.Reflect
open EffectKind (liftEffect le_impure)

set_option linter.unusedSectionVars false

namespace BlockIR.Regroup

variable {d : Dialect} [TyDenote d.Ty] [DialectSignature d] [DialectDenote d]
  [DecidableEq d.Ty] [Monad d.m] [LawfulMonad d.m] [DialectRun d] [DialectLabels d]

/-! ## Splitting a block into straight-line stretches -/

/-- Cut instructions into maximal primop stretches (`inl`) and the control-flow
instructions between them (`inr`). -/
def splitStretches : List (alg d).Instruction → List (List (alg d).Instruction ⊕ (alg d).Instruction)
  | [] => []
  | i :: is =>
    match i.op, splitStretches is with
    | .ofPrimOp _, .inl s :: rest => .inl (i :: s) :: rest
    | .ofPrimOp _, rest => .inl [i] :: rest
    | _, rest => .inr i :: rest

/-- Put the pieces back together. -/
def joinStretches : List (List (alg d).Instruction ⊕ (alg d).Instruction) → List (alg d).Instruction
  | [] => []
  | .inl s :: rest => s ++ joinStretches rest
  | .inr i :: rest => i :: joinStretches rest

theorem join_splitStretches (is : List (alg d).Instruction) :
    joinStretches (splitStretches is) = is := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    rcases i with ⟨regs, op, args⟩
    cases op <;> simp only [splitStretches] <;>
      (try split) <;> simp_all [joinStretches]

/-! ## Reconstructing typed SSA from a stretch -/

/-- Resolve argument registers to typed variables of `Γ`, checking their types. -/
def resolve (Γ : Ctxt d.Ty) (ns : List String) :
    (ts : List d.Ty) → List (alg d).Arg → Option (HVector Γ.Var ts)
  | [], [] => some .nil
  | t :: ts, .ofVar n :: as => do
    let i ← ns.findIdx? (· == n)
    if h : Γ[i]? = some t then
      let vs ← resolve Γ ns ts as
      some (.cons ⟨i, h⟩ vs)
    else none
  | _, _ => none

/-- A partially reconstructed stretch: the context so far, its `Lets`, its registers. -/
structure Acc (d : Dialect) [DialectSignature d] (Γ_in : Ctxt d.Ty) where
  Γ : Ctxt d.Ty
  lets : Lets d Γ_in .impure Γ
  ns : List String

/-- Add one instruction to the reconstructed `Lets`. -/
def step {Γ_in : Ctxt d.Ty} (a : Acc d Γ_in) : (alg d).Instruction → Option (Acc d Γ_in)
  | ⟨regs, .ofPrimOp op, args⟩ =>
    if hr : DialectSignature.regSig op = [] then
      if regs.length = (DialectSignature.returnTypes op).length ∧ (regs ++ a.ns).Nodup then do
        let vs ← resolve a.Γ a.ns (DialectSignature.sig op) args
        let e : Expr d a.Γ .impure (DialectSignature.returnTypes op) :=
          ⟨op, rfl, le_impure _, vs, noRegions hr⟩
        some ⟨e.outContext, .var a.lets e, regs ++ a.ns⟩
      else none
    else none
  | _ => none

def reconstructFrom {Γ_in : Ctxt d.Ty} (a : Acc d Γ_in) :
    List (alg d).Instruction → Option (Acc d Γ_in)
  | [] => some a
  | i :: is => (step a i).bind (reconstructFrom · is)

/-- Rebuild a typed `Lets` from a straight-line stretch, starting from variables of
types `Γ` held in registers `ns`. -/
def reconstruct (Γ : Ctxt d.Ty) (ns : List String) (stretch : List (alg d).Instruction) :
    Option (Acc d Γ) :=
  reconstructFrom ⟨Γ, .nil, ns⟩ stretch

/-! ## Soundness -/

theorem resolve_sound {Γ : Ctxt d.Ty} {ns : List String} :
    ∀ {ts : List d.Ty} {as : List (alg d).Arg} {vs : HVector Γ.Var ts},
      resolve Γ ns ts as = some vs → vars (argNames ns vs) = as
  | [], [], vs, _ => by cases vs; rfl
  | [], _ :: _, _, h => by simp [resolve] at h
  | _ :: _, [], _, h => by simp [resolve] at h
  | t :: ts, .ofData _ :: as, _, h => by simp [resolve] at h
  | t :: ts, .ofVar n :: as, vs, h => by
    simp only [resolve, Option.bind_eq_bind] at h
    rcases hi : ns.findIdx? (· == n) with _ | i
    · simp [hi] at h
    simp only [hi, Option.bind_some] at h
    split at h
    · rename_i hty
      rcases hvs : resolve Γ ns ts as with _ | vs'
      · simp [hvs] at h
      simp only [hvs, Option.bind_some, Option.some.injEq] at h
      subst h
      obtain ⟨hlt, hp, -⟩ := List.findIdx?_eq_some_iff_getElem.1 hi
      have hn : ns[i] = n := by simpa using hp
      simp only [argNames, vars, List.map_cons] at *
      rw [← resolve_sound hvs]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, hn, vars]
    · simp at h

/-- What one reconstruction step guarantees. -/
theorem step_sound {Γ_in : Ctxt d.Ty} {a a' : Acc d Γ_in} {i : (alg d).Instruction}
    (h : step a i = some a') :
    a'.lets.instrs a'.ns = a.lets.instrs a.ns ++ [i] ∧
    (a.lets.RegionFree → a'.lets.RegionFree) ∧
    (∃ pre, a'.ns = pre ++ a.ns ∧ pre.length + a.Γ.length = a'.Γ.length) ∧
    a'.ns.Nodup := by
  rcases i with ⟨regs, op, args⟩
  cases op with
  | call _ => simp [step] at h
  | ret _ => simp [step] at h
  | ofPrimOp op =>
    simp only [step] at h
    split at h
    · rename_i hr
      split at h
      · rename_i hfresh
        rcases hvs : resolve a.Γ a.ns (DialectSignature.sig op) args with _ | vs
        · simp [hvs] at h
        simp only [hvs, Option.bind_eq_bind, Option.bind_some, Option.some.injEq] at h
        subst h
        refine ⟨?_, fun hrf => ⟨hr, hrf⟩, ⟨regs, rfl, ?_⟩, hfresh.2⟩
        · simp only [Lets.instrs, Expr.op, Expr.args]
          rw [← hfresh.1, List.drop_left, List.take_left, resolve_sound hvs]
        · simp [Expr.outContext, Ctxt.length, hfresh.1]
      · simp at h
    · simp at h

theorem reconstructFrom_sound {Γ_in : Ctxt d.Ty} :
    ∀ (a : Acc d Γ_in) (is : List (alg d).Instruction) {a' : Acc d Γ_in},
      reconstructFrom a is = some a' →
      a'.lets.instrs a'.ns = a.lets.instrs a.ns ++ is ∧
      (a.lets.RegionFree → a'.lets.RegionFree) ∧
      (∃ pre, a'.ns = pre ++ a.ns ∧ pre.length + a.Γ.length = a'.Γ.length) ∧
      (a.ns.Nodup → a'.ns.Nodup)
  | a, [], a', h => by
    simp only [reconstructFrom, Option.some.injEq] at h
    subst h
    exact ⟨by simp, id, ⟨[], by simp⟩, id⟩
  | a, i :: is, a', h => by
    simp only [reconstructFrom] at h
    rcases hs : step a i with _ | a₁
    · simp [hs] at h
    simp only [hs, Option.bind_some] at h
    obtain ⟨hi1, hr1, ⟨pre1, hns1, hlen1⟩, hnd1⟩ := step_sound hs
    obtain ⟨hi2, hr2, ⟨pre2, hns2, hlen2⟩, hnd2⟩ := reconstructFrom_sound a₁ is h
    refine ⟨by rw [hi2, hi1]; simp, hr2 ∘ hr1, ⟨pre2 ++ pre1, by simp [hns2, hns1], ?_⟩,
      fun _ => hnd2 hnd1⟩
    simp only [List.length_append]; omega

/-- **Soundness of reconstruction**: a reconstructed stretch is exactly the original
instructions, its `Lets` is region-free, and its registers extend `ns` with fresh ones. -/
theorem reconstruct_sound {Γ : Ctxt d.Ty} {ns : List String} {stretch : List (alg d).Instruction}
    {a : Acc d Γ} (h : reconstruct Γ ns stretch = some a) :
    a.lets.instrs a.ns = stretch ∧ a.lets.RegionFree ∧
    (∃ pre, a.ns = pre ++ ns ∧ pre.length + Γ.length = a.Γ.length) ∧
    (ns.Nodup → a.ns.Nodup) := by
  obtain ⟨hi, hr, hpre, hnd⟩ := reconstructFrom_sound _ _ h
  exact ⟨by simpa [Lets.instrs] using hi, hr trivial, hpre, hnd⟩

/-! ## Using it -/

/-- **Regroup and replace**: if a block starts with a stretch that reconstructs to a
typed `Lets`, running that stretch is its shallow semantics `Lets.denote`. -/
theorem Block.eval_regroup (blocks : List (Block (alg d))) (cs : List Nat)
    {Γ : Ctxt d.Ty} {ns : List String} {stretch rest : List (alg d).Instruction}
    {a : Acc d Γ} (hrec : reconstruct Γ ns stretch = some a)
    (hnd : ns.Nodup) {V : Valuation Γ} {e : Std.HashMap String (Data d)} (hInv : NInv Γ ns V e)
    {s s' : DialectRun.State d} {V' : Valuation a.Γ}
    (hrun : DialectRun.run (d := d) (a.lets.denote V) s = some (V', s')) :
    ∃ e', NInv a.Γ a.ns V' e' ∧
      Block.eval blocks s e cs ⟨[], stretch ++ rest⟩ [] =
        Block.eval blocks s' e' cs ⟨[], rest⟩ [] := by
  obtain ⟨hi, hrf, ⟨pre, hns, hlen⟩, hnd'⟩ := reconstruct_sound hrec
  have hlen' : a.ns.length = a.Γ.length := by rw [hns, ← hlen, List.length_append, hInv.1]
  have hdrop : a.ns.drop (a.ns.length - Γ.length) = ns := by
    rw [hlen', ← hlen, Nat.add_sub_cancel, hns, List.drop_left]
  rw [← hi]
  exact Block.eval_lets blocks cs a.lets hrf a.ns hlen' (hnd' hnd) V e (hdrop ▸ hInv) rest hrun


/-! ## Printing -/

/-- Print a typed `Lets` as one line per op, e.g. `["y"] : [nat] := add(x, x)`. -/
def _root_.Lets.pretty [Repr d.Op] [Repr d.Ty] :
    Lets d Γ_in eff Γ_out → List String → List String
  | .nil, _ => []
  | .var (t := t) body e, ns =>
    body.pretty (ns.drop t.length) ++
      [s!"{ns.take t.length} : {repr t} := {repr e.op}({", ".intercalate
        (argNames (ns.drop t.length) e.args)})"]

/-- Print a reconstructed stretch: its typed SSA and its final context. -/
def Acc.pretty [Repr d.Op] [Repr d.Ty] {Γ_in : Ctxt d.Ty} (a : Acc d Γ_in) : List String :=
  a.lets.pretty a.ns ++ [s!"context: {a.ns.zip (a.Γ.toList.map fun t => s!"{repr t}")}"]

/-- Describe how a block splits: `stretch(n)` for `n` primops, else the op kind. -/
def splitShape (is : List (alg d).Instruction) : List String :=
  (splitStretches is).map fun
    | .inl s => s!"stretch({s.length})"
    | .inr ⟨_, .call _, _⟩ => "call"
    | .inr ⟨_, .ret _, _⟩ => "ret"
    | .inr ⟨_, .ofPrimOp _, _⟩ => "primop"

end BlockIR.Regroup
