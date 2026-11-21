/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.Tactic
import LeanMLIR.BlockIR.Regroup
import LeanMLIR.BlockIR.WellScoped

/-!
# Tactics for BlockIR proofs

`simp_ssa` turns the denotation of typed SSA (`Com`, `Expr`, and the `Lets` that
regrouping extracts from a BlockIR stretch) into plain Lean terms.

It is the repo's `simp_peephole` (the `simp_denote` simp set, which unfolds the
framework's denotations and each dialect's `@[simp_denote]` op semantics) plus the
`Lets.denote` equations. Extra lemmas can be passed as `simp_ssa [foo, bar]`.
-/

open Lean.Parser.Tactic (location)

/-- Unfold the denotation of typed SSA (`Com`, `Expr`, `Lets`) into plain Lean terms. -/
syntax (name := simpSsa) "simp_ssa" (" [" Lean.Parser.Tactic.simpLemma,* "]")? (location)? : tactic

macro_rules
  | `(tactic| simp_ssa $[$loc]?) =>
    `(tactic| simp_ssa [] $[$loc]?)
  | `(tactic| simp_ssa [$lemmas,*] $[$loc]?) =>
    `(tactic| (
      first
      | rw [funext_iff (α := Ctxt.Valuation _)] $[$loc]?
      | change ∀ (_ : Ctxt.Valuation _), _ $[$loc]?
      | skip
      simp (config := {failIfUnchanged := false}) only
        [Expr.denote_castPureToEff, Lets.denote_nil, Lets.denote_var, simp_denote, $lemmas,*]
        $[$loc]?))

/-! ## Unfolding `encode` on explicit vectors

`encode (x ::ₕ xs) = ⟨t, x⟩ :: encode xs` holds by `rfl`, but `simp` can't use the
equation when the vector's index is not syntactically `t :: ts` (e.g. it is
`DialectSignature.returnTypes op`). This `dsimproc` does the unfolding regardless. -/

open Lean Meta in
dsimproc [block_eval] encodeCons (@BlockIR.Shallow.encode _ ?i _ _) := fun e => do
  let args := e.getAppArgs
  if args.size < 2 then return .continue
  let xs ← whnfR args[args.size - 1]!
  let listTy ← whnfR (← inferType e)
  let elemTy := listTy.appArg!
  let some listLvl := listTy.getAppFn.constLevels!.head? | return .continue
  if xs.isAppOfArity ``HVector.cons 6 then
    let cargs := xs.getAppArgs
    let α := cargs[0]!; let f := cargs[1]!; let as := cargs[2]!
    let a := cargs[3]!; let x := cargs[4]!; let xs' := cargs[5]!
    let sigmaTy ← whnfR elemTy
    let head := mkAppN (mkConst ``Sigma.mk sigmaTy.getAppFn.constLevels!) #[α, f, a, x]
    let tail := mkAppN e.getAppFn (args.set! (args.size - 2) as |>.set! (args.size - 1) xs')
    return .visit (mkAppN (mkConst ``List.cons [listLvl]) #[elemTy, head, tail])
  else if xs.isAppOfArity ``HVector.nil 2 then
    return .done (mkAppN (mkConst ``List.nil [listLvl]) #[elemTy])
  else
    return .continue

/-! ## Evaluating a concrete op's signature and semantics

For an op given as a constructor application, `signature op` and
`DialectDenote.denote op args regions` compute by unfolding the dialect's instances.
These `dsimproc`s do that unfolding, so no dialect needs per-op lemmas. -/

open Lean Meta in
/-- Unfold to weak head normal form, but give up on a stuck `match`. -/
private def whnfIfProgress (e : Expr) : MetaM (Option Expr) := do
  let e' ← whnfD e
  if e' == e then return none
  if let some _ ← matchMatcherApp? e' then return none
  return some e'

open Lean Meta in
dsimproc [block_eval] reduceSignature (@DialectSignature.signature _ ?i _) := fun e => do
  let op := e.appArg!
  unless (← isConstructorApp op) do return .continue
  match ← whnfIfProgress e with
  | some e' => return .done e'
  | none => return .continue

open Lean Meta in
open Lean Meta in
/-- `xs` is an explicit vector `x₁ ::ₕ … ::ₕ nil` (its elements may be symbolic). -/
private partial def isHVectorLit (xs : Expr) : MetaM Bool := do
  let xs ← whnfR xs
  if xs.isAppOfArity ``HVector.nil 2 then return true
  if xs.isAppOfArity ``HVector.cons 6 then return ← isHVectorLit xs.appArg!
  return false

open Lean Meta in
dsimproc [block_eval] reduceDenote (@DialectDenote.denote _ _ _ ?i _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 7 do return .continue
  unless (← isConstructorApp args[4]!) do return .continue
  unless (← isHVectorLit args[5]!) do return .continue
  match ← whnfIfProgress e with
  | some e' => return .visit e'
  | none => return .continue

open Lean Meta in
/-- Run a dialect's effects for a concrete `DialectRun` instance (e.g. `Id`, `StateM`). -/
dsimproc [block_eval] reduceRun (@BlockIR.Shallow.DialectRun.run _ _ ?i _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 6 do return .continue
  let inst ← whnfR args[2]!
  unless inst.getAppFn.isConst do return .continue
  match ← whnfIfProgress e with
  | some e' => return .visit e'
  | none => return .continue

open Lean Meta in
/-- Unfold an instance field applied to a concrete instance. -/
private def reduceInstField (e : Expr) (instIdx : Nat) : Simp.SimpM Simp.DStep := do
  let args := e.getAppArgs
  unless args.size > instIdx do return .continue
  let inst ← whnfR args[instIdx]!
  unless inst.getAppFn.isConst do return .continue
  match ← whnfIfProgress e with
  | some e' => return .visit e'
  | none => return .continue

open Lean Meta in
dsimproc [block_eval] reduceLabelTy (@BlockIR.Shallow.DialectLabels.labelTy _ _ ?i) :=
  fun e => reduceInstField e 2
open Lean Meta in
dsimproc [block_eval] reduceOfIdx (@BlockIR.Shallow.DialectLabels.ofIdx _ _ ?i _) :=
  fun e => reduceInstField e 2
open Lean Meta in
dsimproc [block_eval] reduceToIdx (@BlockIR.Shallow.DialectLabels.toIdx _ _ ?i _) :=
  fun e => reduceInstField e 2

/-! ## Finding blocks and instructions

Programs are usually written with helper definitions (`prog`, `dispatch …`, stretches
joined with `++`). These unfold them just enough for the step lemmas to match. -/

open Lean Meta in
/-- `l[i]?` for a literal index into a list that unfolds to an explicit list. -/
dsimproc [block_eval] reduceListGetElem? (@GetElem?.getElem? (List _) Nat _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 7 do return .continue
  let some k := (← instantiateMVars args[6]!).nat? | return .continue
  let elemTy := args[2]!
  let rec walk (l : Expr) : Nat → MetaM (Option Expr)
    | k => do
      let l ← whnfR l
      if l.isAppOfArity ``List.cons 3 then
        if k == 0 then return some (← mkAppOptM ``Option.some #[some elemTy, some l.appFn!.appArg!])
        else walk l.appArg! (k - 1)
      else if l.isAppOfArity ``List.nil 1 then
        return some (← mkAppOptM ``Option.none #[some elemTy])
      else return none
  match ← walk args[5]! k with
  | some r => return .done r
  | none => return .continue

open Lean Meta in
dsimproc [block_eval] reduceBlockArgs (OpAlgebra.Block.args _) := fun e => do
  match ← whnfIfProgress e with
  | some e' => return .visit e'
  | none => return .continue

open Lean Meta in
/-- Unfold an instruction list to an explicit list of `Instruction.mk`s. -/
private partial def normInstrs (l : Expr) : MetaM (Option Expr) := do
  let l ← whnfD l
  if l.isAppOfArity ``List.cons 3 then
    let i ← whnfD l.appFn!.appArg!
    unless i.isAppOfArity ``OpAlgebra.Instruction.mk 4 do return none
    let some rest ← normInstrs l.appArg! | return none
    return some (mkApp2 l.appFn!.appFn! i rest)
  else if l.isAppOfArity ``List.nil 1 then return some l
  else return none

open Lean Meta in
dsimproc [block_eval] reduceBlockInstrs (OpAlgebra.Block.instructions _) := fun e => do
  match ← normInstrs e with
  | some e' => if e' == e then return .continue else return .done e'
  | none => return .continue

open Lean Meta in
/-- Unfold `Block.fn P i args s` when the block index `i` is a numeral (so a call is
unfolded once its target is known, and not before). -/
simproc [block_eval] unfoldBlockFn (@OpAlgebra.Block.fn _ _ _ _ _) := fun e => do
  let args := e.getAppArgs
  unless args.size == 5 do return .continue
  let some _ := (← instantiateMVars args[2]!).nat? | return .continue
  let proof ← mkAppM ``OpAlgebra.Block.fn_unfold #[args[1]!, args[2]!, args[3]!, args[4]!]
  let some (_, _, rhs) := (← inferType proof).eq? | return .continue
  return .visit { expr := rhs, proof? := some proof }

open Lean Meta Elab Tactic in
/-- The closed `Block.fn` calls in `e`, one entry per occurrence. -/
private partial def blockFnCalls (e : Expr) (acc : Array Expr) : Array Expr :=
  let acc := if e.isAppOfArity ``OpAlgebra.Block.fn 5 && !e.hasLooseBVars then acc.push e else acc
  match e with
  | .app f a => blockFnCalls a (blockFnCalls f acc)
  | .lam _ t b _ | .forallE _ t b _ => blockFnCalls b (blockFnCalls t acc)
  | .letE _ t v b _ => blockFnCalls b (blockFnCalls v (blockFnCalls t acc))
  | .mdata _ b | .proj _ _ b => blockFnCalls b acc
  | _ => acc

open Lean Meta Elab Tactic in
/-- Case-split on the result of a call that occurs on both sides of the goal (e.g. the
recursive call in `F (n+1) = (G n).bind …`), so the code after it sees an explicit
result. Fails if there is no such call. -/
elab "block_split" : tactic => withMainContext do
  let t ← instantiateMVars (← getMainTarget)
  let calls := blockFnCalls t #[]
  let shown ← calls.mapM fun c => do return toString (← ppExpr c)
  let mut shared : Option Expr := none
  for i in [0:calls.size] do
    for j in [i+1:calls.size] do
      if shared.isNone && shown[i]! == shown[j]! then
        if ← withReducible (isDefEq calls[i]! calls[j]!) then shared := some calls[i]!
  let some call := shared | throwError "block_split: no shared call"
  let stx ← Term.exprToSyntax call
  evalTactic (← `(tactic| (
    generalize $stx = o
    rcases o with _ | ⟨vs, s'⟩
    · simp only [Option.bind_none]
    rcases vs with _ | ⟨⟨t, a⟩, _ | ⟨⟨t', a'⟩, vs⟩⟩ <;> (try cases t) <;> (try cases t') <;>
      simp only [Option.bind_some])))

/-! ## The rest of the `block_eval` simp set

Normalization the reduction rules need: register lookups, argument lists, `Option`
binds, label and length tests. -/

attribute [block_eval] List.mapM_cons List.mapM_nil OpAlgebra.Arg.instantiate
  Std.HashMap.get?_eq_getElem? Std.HashMap.getElem?_insert Std.HashMap.getElem?_empty
  Option.bind_some Option.bind_none Option.pure_def Option.bind_eq_bind Option.map_some
  Option.map_none DialectSignature.sig DialectSignature.returnTypes DialectSignature.regSig
  DialectSignature.effectKind Function.comp_apply EffectKind.liftEffect_impure
  BlockIR.Shallow.decode List.zip? List.length_cons List.length_nil List.zip_cons_cons
  List.zip_nil_left BlockIR.label BlockIR.Shallow.ofLabel BlockIR.Shallow.toLabel? Id.run_pure
  BlockIR.Shallow.DialectLabels.toIdx_ofIdx List.map_cons List.map_nil cast_eq
  beq_self_eq_true beq_iff_eq Bool.false_eq_true if_true if_false ite_true ite_false dite_true
  ne_eq not_true_eq_false not_false_eq_true Nat.zero_add Nat.add_sub_cancel Nat.add_one_sub_one
  Nat.one_ne_zero Nat.add_one_ne_zero Nat.succ_ne_zero

attribute [block_eval] String.reduceBEq Nat.reduceEqDiff Nat.reduceBEq reduceIte
