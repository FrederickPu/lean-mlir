/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.Mono
import LeanMLIR.RegionCF.Simp

/-!
# Mutually recursive functions, as a region op

```
funcs {
  f(n) = if n == 0 then 0 else 3 * g(n - 1) + n * n + 7
  g(n) = if n == 0 then 1 else 2 * f(n - 1) + n + 5
} in f(n)
```
-/

open Ctxt (Var Valuation)
open TyDenote (toType)

namespace RegionCF.MutualRec

/-! ## Building programs -/

abbrev Com (Γ : Ctxt Ty) (ty : List Ty) := _root_.Com CF Γ .impure ty

/-- An instruction. -/
abbrev E {Γ : Ctxt Ty} (op : Op) (args : HVector (Var Γ) (DialectSignature.sig (d := CF) op))
    (regs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2)
      (DialectSignature.regSig (d := CF) op) := by exact .nil) :
    Expr CF Γ .impure (DialectSignature.returnTypes (d := CF) op) :=
  ⟨op, rfl, EffectKind.le_impure _, args, regs⟩

/-- Variable `i` of the context (its type checked by `rfl`). -/
abbrev v {Γ : Ctxt Ty} {t : Ty} (i : Nat) (h : Γ[i]? = some t := by rfl) : Var Γ t := ⟨i, h⟩

abbrev N := Ty.nat
abbrev F := Ty.fn 1 1

/-- A function body `h(n) = if n == 0 then k else c * other(n - 1) + body`, with `other` the
function at position `o` of the group `[f, g]`. -/
def fBody : Com ⟨[F, F, N]⟩ [N] :=
  .var (E .eqz (.cons (v 2) .nil)) <|                                 -- z, f, g, n
  .var (E (.ite [F, N] [N]) (.cons (v 0) (.cons (v 2) (.cons (v 3) .nil)))
    (.cons
      -- n == 0: 0
      (.var (E (.cst 0) .nil) <| .rets (.cons (v 0) .nil))
      (.cons
        -- else: 3 * g(n - 1) + n * n + 7
        (.var (E (.cst 1) .nil) <|                                    -- one, g, n
         .var (E .sub (.cons (v 2) (.cons (v 0) .nil))) <|            -- m, one, g, n
         .var (E (.call 1 1) (.cons (v 2) (.cons (v 0) .nil))) <|     -- a, m, one, g, n
         .var (E (.cst 3) .nil) <|                                    -- three, a, m, one, g, n
         .var (E .mul (.cons (v 0) (.cons (v 1) .nil))) <|            -- b, three, a, …, n
         .var (E .mul (.cons (v 6) (.cons (v 6) .nil))) <|            -- sq, b, …
         .var (E .add (.cons (v 1) (.cons (v 0) .nil))) <|            -- c, sq, b, …
         .var (E (.cst 7) .nil) <|                                    -- seven, c, …
         .var (E .add (.cons (v 1) (.cons (v 0) .nil))) <|            -- res, seven, c, …
         .rets (.cons (v 0) .nil))
        .nil))) <|
  .rets (.cons (v 0) .nil)

def gBody : Com ⟨[F, F, N]⟩ [N] :=
  .var (E .eqz (.cons (v 2) .nil)) <|                                 -- z, f, g, n
  .var (E (.ite [F, N] [N]) (.cons (v 0) (.cons (v 1) (.cons (v 3) .nil)))
    (.cons
      (.var (E (.cst 1) .nil) <| .rets (.cons (v 0) .nil))
      (.cons
        -- else: 2 * f(n - 1) + n + 5
        (.var (E (.cst 1) .nil) <|                                    -- one, f, n
         .var (E .sub (.cons (v 2) (.cons (v 0) .nil))) <|            -- m, one, f, n
         .var (E (.call 1 1) (.cons (v 2) (.cons (v 0) .nil))) <|     -- a, m, one, f, n
         .var (E (.cst 2) .nil) <|                                    -- two, a, …
         .var (E .mul (.cons (v 0) (.cons (v 1) .nil))) <|            -- b, two, a, …, n
         .var (E .add (.cons (v 0) (.cons (v 6) .nil))) <|            -- c, b, …
         .var (E (.cst 5) .nil) <|                                    -- five, c, …
         .var (E .add (.cons (v 1) (.cons (v 0) .nil))) <|            -- res, five, c, …
         .rets (.cons (v 0) .nil))
        .nil))) <|
  .rets (.cons (v 0) .nil)

/-- `funcs { f; g } in f(n)` -/
def prog : Com ⟨[N]⟩ [N] :=
  .var (E (.funcs [(1, 1), (1, 1)] [N] [N]) (.cons (v 0) .nil)
    (.cons
      -- main: f(n)       (context: f, g, n)
      (.var (E (.call 1 1) (.cons (v 0) (.cons (v 2) .nil))) <| .rets (.cons (v 0) .nil))
      (.cons fBody (.cons gBody .nil)))) <|
  .rets (.cons (v 0) .nil)

/-! ## The specification -/

mutual
def f : Nat → Nat
  | 0 => 0
  | n + 1 => 3 * g n + (n + 1) * (n + 1) + 7
def g : Nat → Nat
  | 0 => 1
  | n + 1 => 2 * f n + (n + 1) + 5
end

/-- `f`, computed by the program. -/
def F' (n : Nat) : Option Nat :=
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (r.head : Nat)

#guard (List.range 8).all fun n => F' n == some (f n)

/-! ## The proof

Each body, run on its arguments (`cf_reduce` evaluates the program), is its equation; the
table of the group is monotone, so it is the fixpoint of its bodies (`funcsFix_unfold`); by
induction, it is `f` and `g`. -/

open Lean.Order

theorem fBody_denote (fv gv : List Nat → Option (List Nat)) (n : Nat) :
    fBody.denote (Valuation.ofHVector (fv ::ₕ gv ::ₕ (n : Nat) ::ₕ .nil)) =
      if n = 0 then some ((0 : Nat) ::ₕ .nil) else
        (gv [n - 1]).bind fun r => (ofNats 1 r).bind fun a =>
          some ((3 * (a.head : Nat) + n * n + 7 : Nat) ::ₕ .nil) := by
  unfold fBody
  cases n with
  | zero => rfl
  | succ n =>
    cf_reduce
    simp only [Option.bind_assoc, Nat.add_sub_cancel]
    cf_reduce
    congr 1; funext r
    rcases ofNats 1 r with _ | (_ | ⟨x, xs⟩)
    · rfl
    · cases xs; rfl

theorem gBody_denote (fv gv : List Nat → Option (List Nat)) (n : Nat) :
    gBody.denote (Valuation.ofHVector (fv ::ₕ gv ::ₕ (n : Nat) ::ₕ .nil)) =
      if n = 0 then some ((1 : Nat) ::ₕ .nil) else
        (fv [n - 1]).bind fun r => (ofNats 1 r).bind fun a =>
          some ((2 * (a.head : Nat) + n + 5 : Nat) ::ₕ .nil) := by
  unfold gBody
  cases n with
  | zero => rfl
  | succ n =>
    cf_reduce
    simp only [Option.bind_assoc, Nat.add_sub_cancel]
    cf_reduce
    congr 1; funext r
    rcases ofNats 1 r with _ | (_ | ⟨x, xs⟩)
    · rfl
    · cases xs; rfl

/-- The bodies of `f` and `g`, as a table transformer. -/
abbrev Fb : FnTable → FnTable := fun T =>
  bodies [(1, 1), (1, 1)] T [(1, 1), (1, 1)] (Com.denote fBody ::ₕ Com.denote gBody ::ₕ .nil)

/-- The functions of the program. -/
noncomputable abbrev T : FnTable := funcsFix Fb

/-- The bodies, as the `funcs` op's regions. -/
def bodyRegs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2)
    ([(1, 1), (1, 1)].map fun (n, m) => (⟨fnTys [(1, 1), (1, 1)] ++ nats n⟩, nats m)) :=
  .cons fBody (.cons gBody .nil)

/-- The bodies are monotone: true of every program (`Com.denote_mono`). -/
theorem hFb : RegsMono (HVector.denote (d := CF) bodyRegs) := HVector.denote_mono bodyRegs

/-- Each function's equation: `funcsFix_apply`, for any group, with monotonicity from the
general theorem (`HVector.denote_mono`); the rest is computation. -/
theorem T_f (n : Nat) :
    T 0 [n] = Option.map (toNats (n := 1))
      (fBody.denote (Valuation.ofHVector (T 0 ::ₕ T 1 ::ₕ (n : Nat) ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 0 [n]).trans rfl
theorem T_g (n : Nat) :
    T 1 [n] = Option.map (toNats (n := 1))
      (gBody.denote (Valuation.ofHVector (T 0 ::ₕ T 1 ::ₕ (n : Nat) ::ₕ .nil))) :=
  (funcsFix_apply _ _ hFb 1 [n]).trans rfl

theorem table : (n : Nat) → T 0 [n] = some [f n] ∧ T 1 [n] = some [g n]
  | 0 => by rw [T_f, T_g, fBody_denote, gBody_denote]; simp [f, g]; exact ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨ihf, ihg⟩ := table n
    rw [T_f, T_g, fBody_denote, gBody_denote]
    simp [ihf, ihg, f, g, ofNats]; exact ⟨rfl, rfl⟩

/-- **The program computes `f`.** -/
theorem F'_eq (n : Nat) : F' n = some (f n) := by
  unfold F' prog
  cf_reduce
  have h : funcsFix Fb 0 [n] = some [f n] := (table n).1
  rw [h]
  rfl

end RegionCF.MutualRec
