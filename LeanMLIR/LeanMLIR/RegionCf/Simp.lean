/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Framework

/-!
# Looking up variables by their literal index

Programs written by hand name variables as `⟨i, h⟩` with `i` a literal. These lemmas look
them up in an `HVector` (what `Valuation.ofHVector_apply` leaves) and in a `Valuation`
built by `::ᵥ`, one position at a time.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)

namespace RegionCfFunctor

variable {α : Type} {A : α → Type} {a t : α} {as : List α} {Γ : Ctxt α}

@[simp] theorem HVector.getElem_lit_zero (x : A a) (xs : HVector A as)
    (h : Γ[0]? = some a) (p : a :: as = Γ.toList) :
    @GetElem.getElem _ (Var Γ a) _ _ _ (HVector.cons x xs) (Subtype.mk 0 h) p = x := by
  rcases Γ with ⟨Γ⟩; cases p; rfl

@[simp] theorem HVector.getElem_lit_succ (x : A a) (xs : HVector A as) (i : Nat)
    (h : Γ[i + 1]? = some t) (p : a :: as = Γ.toList) :
    @GetElem.getElem _ (Var Γ t) _ _ _ (HVector.cons x xs) (Subtype.mk (i + 1) h) p =
      @GetElem.getElem _ (Var (Ctxt.ofList as) t) _ _ _ xs
        (Subtype.mk i (by rcases Γ with ⟨Γ⟩; cases p; exact h)) rfl := by
  rcases Γ with ⟨Γ⟩; cases p; rfl

variable {Ty : Type} [TyDenote Ty] {Γ : Ctxt Ty} {s u : Ty}

@[simp] theorem Valuation.cons_lit_zero (x : toType s) (V : Γ.Valuation)
    (h : (Γ.cons s)[0]? = some s) :
    (x ::ᵥ V) (Subtype.mk 0 h : Var (Γ.cons s) s) = x := rfl

@[simp] theorem Valuation.cons_lit_succ (x : toType s) (V : Γ.Valuation) (i : Nat)
    (h : (Γ.cons s)[i + 1]? = some u) :
    (x ::ᵥ V) (Subtype.mk (i + 1) h : Var (Γ.cons s) u) = V (Subtype.mk i h : Var Γ u) := rfl



/-! ## `cf_reduce`: run a program's denotation as far as it goes

The denotation of a program written out in full (literal variable indices, known ops)
reduces by unfolding: `Com.denote`, the lookups, `some x >>= f`. `cf_reduce` does exactly
this to every subterm of the goal, by definitional unfolding of the framework's and the
dialect's own definitions only, so it stops at what is not known (a function argument
applied, an `if` on a variable) and leaves Lean's own operations (`ite`, `+`, …) alone. -/

open Lean Meta Elab Tactic

namespace CFReduce

/-- The definitions `cf_reduce` unfolds. -/
def unfoldable (n : Name) : Bool :=
  (n.getRoot matches `Ctxt | `HVector | `Com | `Expr | `RegionCfFunctor | `EffectKind | `DialectDenote
    | `DialectSignature | `Signature) ||
  n matches ``Option.bind | ``Option.map | ``cast | ``Eq.mpr | ``Eq.mp | ``Fin.cast
    | ``Function.comp | `Option.instMonad | `Option.instFunctor
    | ``instHAppendOfAppend | ``Ctxt.instAppend

/-- The classes whose instances `cf_reduce` keeps: Lean's arithmetic and decisions. -/
def keptClass (n : Name) : Bool :=
  n matches ``Decidable | ``DecidableEq | ``HAdd | ``Add | ``HSub | ``Sub | ``HMul | ``Mul
    | ``HDiv | ``Div | ``HMod | ``Mod | ``HPow | ``Pow | ``OfNat | ``NatCast | ``LE | ``LT
    | ``BEq | ``Hashable | ``Max | ``Min | ``Repr | ``ToString

/-- May `cf_reduce` unfold this constant? Everything but `if` (decided separately, by
`decideIte`) and the fixpoints. -/
def canUnfold (_ : Meta.Config) (c : ConstantInfo) : CoreM Bool :=
  return !(c.name matches `RegionCfFunctor.funcsFix | `RegionCfFunctor.whileLoop | ``ite | ``dite)

/-- Is `e` Lean's arithmetic (`a + b`, …), which `cf_reduce` leaves as it is? -/
def isArith (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  let some info := (← getEnv).getProjectionFnInfo? c | return false
  return keptClass info.ctorName.getPrefix

/-- Is `e` stuck on a `match` (or a recursor) that does not reduce? -/
def isStuck (e : Expr) : MetaM Bool := do
  let .const c _ := e.getAppFn | return false
  return (← isMatcher c) || (← isRec c) || isCasesOnRecursor (← getEnv) c

/-- Reduce `e`: unfold its head while that makes progress (a definition whose `match`
reduces, an instance projection), never into a `match` that is stuck. -/
partial def step (e : Expr) (fuel : Nat := 512) : MetaM Expr :=
  withTransparency .all <| withCanUnfoldPred canUnfold do
    let e ← whnfCore e
    if fuel = 0 then return e
    let .const c _ := e.getAppFn | return e
    let some info := (← getEnv).find? c | return e
    unless ← canUnfold {} info do return e
    if ← isArith e then return e
    let e' ← if (← getEnv).isProjectionFn c then unfoldProjInst? e else unfoldDefinition? e
    let some e' := e' | return e
    let e'' ← whnfCore e'
    if ← isStuck e'' then return e
    step e'' (fuel - 1)

/-- An `if` whose condition decides: its branch. -/
def decideIte (e : Expr) : MetaM (Option Expr) := do
  let isIte := e.isAppOf ``ite && e.getAppNumArgs ≥ 5
  let isDite := e.isAppOf ``dite && e.getAppNumArgs ≥ 5
  unless isIte || isDite do return none
  let args := e.getAppArgs
  let d ← withTransparency .all <| whnf args[2]!
  let rest := args.extract 5 args.size
  if d.isAppOfArity ``Decidable.isTrue 2 then
    return some (mkAppN (if isDite then mkApp args[3]! d.appArg! else args[3]!) rest).headBeta
  if d.isAppOfArity ``Decidable.isFalse 2 then
    return some (mkAppN (if isDite then mkApp args[4]! d.appArg! else args[4]!) rest).headBeta
  return none

/-- Reduce every data subterm of `e` (not functions, types or proofs). -/
def reduceAll (e : Expr) : MetaM Expr :=
  transform e (post := fun e => do
    if e.isApp && !(← isProp e) && !(← isType e) && !(← isProof e) then
      if let some e' ← decideIte e then return .done e'
      let ty ← whnf (← inferType e)
      if ty.isForall || (← isClass? ty).isSome then return .continue
      if let some e' ← decideIte e then return .done e'
      if ← isArith e then return .continue
      let e' ← step e
      if e' != e then return .done e'
    return .continue)

end CFReduce

/-- Run the denotation of the programs in the goal as far as it goes (see `CFReduce`). -/
elab "cf_reduce" : tactic => withMainContext do
  let g ← getMainGoal
  let mut t ← instantiateMVars (← g.getType)
  for _ in [0:100] do
    let t' ← zetaReduce (← CFReduce.reduceAll t)
    if t' == t then break
    t := t'
  replaceMainGoal [← g.replaceTargetDefEq t]

/-- `cf_reduce`, then normalize the binds it leaves at what is unknown (a call to an unknown
function, a `match` on its result): reassociate them, push the `.map`s of multi-result
ops through, and reduce again. Repeated twice, as normalizing can expose more to reduce. -/
macro "cf_simp" : tactic => `(tactic| (
  iterate 2
    cf_reduce
    try simp only [Option.bind_assoc, Option.bind_map, Option.map_bind, Option.map_map,
      Function.comp_def, Nat.add_sub_cancel]
  cf_reduce))
