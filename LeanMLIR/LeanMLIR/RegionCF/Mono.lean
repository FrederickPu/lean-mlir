/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.Dialect

/-!
# Every program is monotone in its functions

Order values by definedness: a function is below another if, on every input, it has no value
or the same one (`⊑` of `Option`); numbers only below themselves. Then every program's
denotation is monotone (`Com.denote_mono`): running it on a valuation below another gives a
result below. In particular every group of functions is monotone in the functions it calls
(`bodies_monotone`), so `funcsFix_unfold` applies: **the equations of any group of mutually
recursive functions hold** (`funcsFix_bodies_unfold`), with no proof left to the program.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)
open Lean.Order

namespace RegionCF

/-! ## The order -/

/-- Values, by definedness: numbers equal, functions pointwise `⊑`. -/
def ValLe : (t : Ty) → toType t → toType t → Prop
  | .nat, a, b => a = b
  | .fn _ _, f, g => ∀ xs, f xs ⊑ g xs

/-- Vectors of values, pointwise. -/
inductive HVLe : {ts : List Ty} → HVector toType ts → HVector toType ts → Prop
  | nil : HVLe .nil .nil
  | cons {t : Ty} {ts : List Ty} {a b : toType t} {as bs : HVector toType ts} :
      ValLe t a b → HVLe as bs → HVLe (.cons a as) (.cons b bs)

/-- Valuations, pointwise. -/
def VLe {Γ : Ctxt Ty} (V W : Γ.Valuation) : Prop := ∀ t (v : Γ.Var t), ValLe t (V v) (W v)

/-- Results: no value is below anything; a value only below a value above it. -/
def OptLe {α : Type} (R : α → α → Prop) : Option α → Option α → Prop
  | none, _ => True
  | some a, some b => R a b
  | some _, none => False

/-- A region: below valuations give below results. -/
def RegMono {t : Ctxt Ty × List Ty} (r : t.1.Valuation → Option (HVector toType t.2)) : Prop :=
  ∀ V W, VLe V W → OptLe HVLe (r V) (r W)

/-- All regions of an op. -/
inductive RegsMono : {l : List (Ctxt Ty × List Ty)} →
    HVector (fun t : Ctxt Ty × List Ty => t.1.Valuation → Option (HVector toType t.2)) l → Prop
  | nil : RegsMono .nil
  | cons {t : Ctxt Ty × List Ty} {l : List (Ctxt Ty × List Ty)}
      {r : t.1.Valuation → Option (HVector toType t.2)}
      {rs : HVector (fun t : Ctxt Ty × List Ty => t.1.Valuation → Option (HVector toType t.2)) l} :
      RegMono r → RegsMono rs → RegsMono (.cons r rs)

/-! ## Basic facts -/

theorem ValLe.refl : (t : Ty) → (a : toType t) → ValLe t a a
  | .nat, _ => rfl
  | .fn _ _, _ => fun _ => PartialOrder.rel_refl

theorem HVLe.refl : {ts : List Ty} → (xs : HVector toType ts) → HVLe xs xs
  | [], .nil => .nil
  | t :: _, .cons a as => .cons (ValLe.refl t a) (HVLe.refl as)

/-- Below vectors of numbers are equal. -/
theorem HVLe.nats_eq : {n : Nat} → {xs ys : HVector toType (nats n)} → HVLe xs ys → xs = ys
  | 0, .nil, .nil, _ => rfl
  | _ + 1, .cons _ _, .cons _ _, .cons h hs => by
    cases (h : _ = _); rw [HVLe.nats_eq hs]

theorem OptLe.bind {α β : Type} {R : α → α → Prop} {S : β → β → Prop} {a a' : Option α}
    {f g : α → Option β} (h : OptLe R a a') (hf : ∀ x x', R x x' → OptLe S (f x) (g x')) :
    OptLe S (a.bind f) (a'.bind g) := by
  rcases a with _ | x <;> rcases a' with _ | x' <;> first | trivial | exact hf _ _ h

theorem OptLe.of_rel {α : Type} {R : α → α → Prop} (hR : ∀ x, R x x) {a a' : Option α}
    (h : a ⊑ a') : OptLe R a a' := by
  cases h
  · trivial
  · rcases a with _ | x
    · trivial
    · exact hR x

theorem OptLe.refl {α : Type} {R : α → α → Prop} (hR : ∀ x, R x x) (a : Option α) :
    OptLe R a a := OptLe.of_rel hR PartialOrder.rel_refl

theorem OptLe.to_rel {α : Type} {a a' : Option α} (h : OptLe Eq a a') : a ⊑ a' := by
  rcases a with _ | x <;> rcases a' with _ | x'
  · exact FlatOrder.rel.bot
  · exact FlatOrder.rel.bot
  · cases h
  · cases (h : x = x'); exact FlatOrder.rel.refl

theorem VLe.cons {Γ : Ctxt Ty} {t : Ty} {x y : toType t} {V W : Γ.Valuation}
    (h : ValLe t x y) (hV : VLe V W) : VLe (x ::ᵥ V) (y ::ᵥ W) := by
  intro u v
  cases v using Var.casesOn
  · simpa using hV _ _
  · simpa using h

theorem VLe.ofHVector : {ts : List Ty} → {xs ys : HVector toType ts} → HVLe xs ys →
    VLe (Valuation.ofHVector xs) (Valuation.ofHVector ys)
  | [], .nil, .nil, _ => fun _ v => v.emptyElim
  | _ :: _, .cons _ _, .cons _ _, .cons h hs => VLe.cons h (VLe.ofHVector hs)

theorem VLe.append {Γ Δ : Ctxt Ty} {V V' : Γ.Valuation} {W W' : Δ.Valuation}
    (hV : VLe V V') (hW : VLe W W') : VLe (V ++ W) (V' ++ W') := by
  intro t v
  refine Var.appendCases (motive := fun v => ValLe t ((V ++ W) v) ((V' ++ W') v)) ?_ ?_ v
  · intro v; simpa using hV _ v
  · intro v; simpa using hW _ v

theorem VLe.cast {Γ Δ : Ctxt Ty} (h : Γ = Δ) {V W : Γ.Valuation} (hV : VLe V W) :
    VLe (V.cast h) (W.cast h) := by
  subst h; simpa using hV

theorem HVLe.map {Γ : Ctxt Ty} {V W : Γ.Valuation} (hV : VLe V W) :
    {ts : List Ty} → (vs : HVector (Var Γ) ts) → HVLe (vs.map V) (vs.map W)
  | [], .nil => .nil
  | _ :: _, .cons v vs => .cons (hV _ v) (HVLe.map hV vs)

/-! ## The fixpoints

`whileLoop` and `funcsFix` respect the order, by fixpoint induction. -/

/-- A loop whose body respects a relation on states respects it. -/
theorem whileLoop_rel {α : Type} (R : α → α → Prop) (b : α → Option (Nat × α))
    (hb : ∀ x x', R x x' → OptLe (fun p q => p.1 = q.1 ∧ R p.2 q.2) (b x) (b x')) :
    ∀ x x', R x x' → OptLe R (whileLoop b x) (whileLoop b x') := by
  refine whileLoop.fixpoint_induct b
    (fun w => ∀ x x', R x x' → OptLe R (w x) (whileLoop b x')) ?_ ?_
  · apply admissible_pi; intro x
    apply admissible_pi; intro x'
    apply admissible_pi; intro _
    exact admissible_apply (fun x o => OptLe R o (whileLoop b x')) x
      (admissible_flatOrder _ trivial)
  · intro w hw x x' hx
    rw [whileLoop_unfold]
    refine OptLe.bind (hb x x' hx) ?_
    rintro ⟨c, y⟩ ⟨c', y'⟩ ⟨hc, hy⟩
    simp only at hc; subst hc
    dsimp only
    split
    · exact hy
    · exact hw y y' hy

/-! ## Every op respects the order -/

/-- `ofNats` of the same list. -/
theorem OptLe.ofNats (m : Nat) {a a' : Option (List Nat)} (h : a ⊑ a') :
    OptLe HVLe (a.bind (ofNats m)) (a'.bind (ofNats m)) :=
  OptLe.bind (OptLe.of_rel (R := Eq) (fun _ => rfl) h) fun _ _ e => e ▸ OptLe.refl HVLe.refl _

theorem fnVals_le {T T' : FnTable} (h : T ⊑ T') :
    (sigs : List (Nat × Nat)) → (i : Nat) → HVLe (fnVals T sigs i) (fnVals T' sigs i)
  | [], _ => .nil
  | _ :: sigs, i => .cons (fun xs => h i xs) (fnVals_le h sigs (i + 1))

/-- Vectors side by side. -/
theorem HVLe.append : {as bs : List Ty} → {xs xs' : HVector toType as} →
    {ys ys' : HVector toType bs} → HVLe xs xs' → HVLe ys ys' → HVLe (xs ++ ys) (xs' ++ ys')
  | [], _, .nil, .nil, _, _, _, h => h
  | _ :: _, _, .cons _ _, .cons _ _, _, _, .cons h hs, h' => .cons h (HVLe.append hs h')

/-- **A group of functions is monotone in the functions it calls**, if its bodies are. -/
theorem bodies_monotone (sigs₀ : List (Nat × Nat)) : (sigs : List (Nat × Nat)) →
    (rs : HVector (fun t : Ctxt Ty × List Ty => t.1.Valuation → Option (HVector toType t.2))
      (sigs.map fun (n, m) => (⟨fnTys sigs₀ ++ nats n⟩, nats m))) → RegsMono rs →
    monotone fun T => bodies sigs₀ T sigs rs
  | [], .nil, _ => fun _ _ _ => PartialOrder.rel_refl
  | (n, m) :: sigs, .cons r rs, .cons hr hrs => by
    intro T T' h i xs
    simp only [bodies]
    split
    · refine OptLe.to_rel (OptLe.bind (OptLe.refl (fun _ => rfl) _) ?_)
      rintro ys _ rfl
      have := hr _ _ (VLe.ofHVector (ts := fnTys sigs₀ ++ nats n)
        (xs := fnVals T sigs₀ ++ ys) (ys := fnVals T' sigs₀ ++ ys) ?_)
      · rcases hv : r (Valuation.ofHVector (fnVals T sigs₀ ++ ys)) with _ | a <;>
          rcases hv' : r (Valuation.ofHVector (fnVals T' sigs₀ ++ ys)) with _ | a' <;>
          rw [hv, hv'] at this
        · trivial
        · trivial
        · cases this
        · exact congrArg toNats (HVLe.nats_eq this)
      · exact HVLe.append (fnVals_le h sigs₀ 0) (HVLe.refl ys)
    · exact bodies_monotone sigs₀ sigs rs hrs T T' h (i - 1) xs

/-- **Every op respects the order**: arguments below give results below, for monotone
regions. -/
theorem denote_mono (op : Op) (heff : DialectSignature.effectKind (d := CF) op ≤ .impure)
    (xs ys : HVector toType (DialectSignature.sig (d := CF) op)) (hxy : HVLe xs ys)
    (rs : HVector (fun t : Ctxt Ty × List Ty => t.1.Valuation → EffectKind.impure.toMonad CF.m (HVector toType t.2))
      (DialectSignature.regSig (d := CF) op)) (hrs : RegsMono rs) :
    OptLe HVLe (EffectKind.liftEffect heff (DialectDenote.denote (d := CF) op xs rs))
      (EffectKind.liftEffect heff (DialectDenote.denote (d := CF) op ys rs)) := by
  cases op with
  | cst k => exact OptLe.refl HVLe.refl _
  | add | sub | mul =>
    rcases xs with _ | ⟨a, _ | ⟨b, ⟨⟩⟩⟩; rcases ys with _ | ⟨a', _ | ⟨b', ⟨⟩⟩⟩
    obtain _ | ⟨rfl, _ | ⟨rfl, -⟩⟩ := hxy
    exact OptLe.refl HVLe.refl _
  | eqz =>
    rcases xs with _ | ⟨a, ⟨⟩⟩; rcases ys with _ | ⟨a', ⟨⟩⟩
    obtain _ | ⟨rfl, -⟩ := hxy
    exact OptLe.refl HVLe.refl _
  | ite ts rs' =>
    rcases xs with _ | ⟨c, xs⟩; rcases ys with _ | ⟨c', ys⟩
    obtain _ | ⟨rfl, hxy⟩ := hxy
    rcases rs with _ | ⟨thn, _ | ⟨els, ⟨⟩⟩⟩
    obtain _ | ⟨hthn, _ | ⟨hels, -⟩⟩ := hrs
    change OptLe HVLe (if (show Nat from c) ≠ 0 then _ else _) (if (show Nat from c) ≠ 0 then _ else _)
    split
    · exact hthn _ _ (VLe.ofHVector hxy)
    · exact hels _ _ (VLe.ofHVector hxy)
  | «while» ts =>
    rcases rs with _ | ⟨body, ⟨⟩⟩
    obtain _ | ⟨hbody, -⟩ := hrs
    refine whileLoop_rel HVLe _ ?_ xs ys hxy
    intro st st' hst
    have := hbody _ _ (VLe.ofHVector hst)
    revert this
    rcases body (Valuation.ofHVector st) with _ | r <;>
      rcases body (Valuation.ofHVector st') with _ | r' <;> intro this
    · trivial
    · trivial
    · exact this.elim
    · cases this with
      | cons hc hr => exact And.intro hc hr
  | funcs sigs ts rs' =>
    rcases rs with _ | ⟨main, regs⟩
    obtain _ | ⟨hmain, -⟩ := hrs
    exact hmain _ _ (VLe.ofHVector (HVLe.append (HVLe.refl _) hxy))
  | call n m =>
    rcases xs with _ | ⟨f, xs⟩; rcases ys with _ | ⟨f', ys⟩
    obtain _ | ⟨hf, hxy⟩ := hxy
    cases HVLe.nats_eq hxy
    exact OptLe.ofNats m (hf _)

/-! ## Every program respects the order -/

/-- A denotation of effect `.impure`, as an `Option`. -/
def toOpt {eff : EffectKind} {α : Type} (h : eff = .impure) (x : eff.toMonad Option α) : Option α :=
  match eff, h with
  | _, rfl => x

mutual

theorem Com.denote_mono {Γ : Ctxt Ty} {eff : EffectKind} {ty : List Ty} :
    (c : _root_.Com CF Γ eff ty) → (heff : eff = .impure) → ∀ V W, VLe V W →
      OptLe HVLe (toOpt heff (c.denote V)) (toOpt heff (c.denote W))
  | .rets vs, heff, V, W, h => by subst heff; exact HVLe.map h vs
  | .var e body, heff, V, W, h => by
    have he := Expr.denote_mono e heff V W h
    have hb := fun V W h => Com.denote_mono body heff V W h
    subst heff
    exact OptLe.bind (f := body.denote) (g := body.denote) he hb

theorem Expr.denote_mono {Γ : Ctxt Ty} {eff : EffectKind} {ty : List Ty} :
    (e : _root_.Expr CF Γ eff ty) → (heff : eff = .impure) → ∀ V W, VLe V W →
      OptLe VLe (toOpt heff (e.denote V)) (toOpt heff (e.denote W))
  | ⟨op, ty_eq, hop, args, regArgs⟩, heff, V, W, h => by
    have hr := HVector.denote_mono regArgs
    subst heff
    refine OptLe.bind (S := VLe) (denote_mono op hop _ _ (HVLe.map h args) _ hr) ?_
    intro x y h'
    exact VLe.cast _ (VLe.append (VLe.ofHVector h') h)

theorem HVector.denote_mono {l : List (Ctxt Ty × List Ty)} :
    (rs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2) l) →
      RegsMono (HVector.denote (d := CF) rs)
  | .nil => .nil
  | .cons r rs => .cons (Com.denote_mono r rfl) (HVector.denote_mono rs)

end

/-- **The equations of a group of mutually recursive functions**, for any program: the table
is its bodies, calling the table. -/
theorem funcsFix_bodies_unfold (sigs : List (Nat × Nat))
    (regs : HVector (fun t : Ctxt Ty × List Ty => _root_.Com CF t.1 .impure t.2)
      (sigs.map fun (n, m) => (⟨fnTys sigs ++ nats n⟩, nats m))) :
    funcsFix (fun T => bodies sigs T sigs (HVector.denote (d := CF) regs)) =
      bodies sigs (funcsFix fun T => bodies sigs T sigs (HVector.denote (d := CF) regs)) sigs (HVector.denote (d := CF) regs) :=
  funcsFix_unfold (bodies_monotone sigs sigs _ (HVector.denote_mono regs))

/-! ## Each function's equation

`funcsFix_apply` unfolds the table once at any index; `bodies_zero`/`bodies_succ` then pick
out that function's body. Together, for any group and any `i` with body `rᵢ` taking `n`
numbers: `T i xs = (ofNats n xs).bind fun ys => (rᵢ (fnVals T sigs ++ ys)).map toNats`. -/

@[simp] theorem bodies_zero (sigs₀ : List (Nat × Nat)) (T : FnTable) (n m : Nat)
    (sigs : List (Nat × Nat)) (r : RegFn (⟨fnTys sigs₀ ++ nats n⟩, nats m))
    (rs : HVector RegFn (sigs.map fun (n, m) => (⟨fnTys sigs₀ ++ nats n⟩, nats m)))
    (xs : List Nat) :
    bodies sigs₀ T ((n, m) :: sigs) (.cons r rs) 0 xs =
      (ofNats n xs).bind fun ys => (r (Valuation.ofHVector (fnVals T sigs₀ ++ ys))).map toNats :=
  rfl

@[simp] theorem bodies_succ (sigs₀ : List (Nat × Nat)) (T : FnTable) (n m : Nat)
    (sigs : List (Nat × Nat)) (r : RegFn (⟨fnTys sigs₀ ++ nats n⟩, nats m))
    (rs : HVector RegFn (sigs.map fun (n, m) => (⟨fnTys sigs₀ ++ nats n⟩, nats m)))
    (i : Nat) (xs : List Nat) :
    bodies sigs₀ T ((n, m) :: sigs) (.cons r rs) (i + 1) xs = bodies sigs₀ T sigs rs i xs := by
  simp [bodies]

@[simp] theorem ofNats_zero : ofNats 0 [] = some .nil := rfl
@[simp] theorem ofNats_succ (n x : Nat) (xs : List Nat) :
    ofNats (n + 1) (x :: xs) = (ofNats n xs).map (.cons (x : Nat)) := rfl
@[simp] theorem toNats_nil : toNats (n := 0) .nil = [] := rfl
@[simp] theorem toNats_cons (n x : Nat) (xs : HVector toType (nats n)) :
    toNats (n := n + 1) (.cons (x : Nat) xs) = x :: toNats xs := rfl
@[simp] theorem fnVals_nil (T : FnTable) (i : Nat) : fnVals T [] i = .nil := rfl
@[simp] theorem fnVals_cons (T : FnTable) (s : Nat × Nat) (sigs : List (Nat × Nat)) (i : Nat) :
    fnVals T (s :: sigs) i = .cons (T i) (fnVals T sigs (i + 1)) := rfl

/-- **One function of a group, unfolded once**: for monotone bodies (every program's are,
`HVector.denote_mono`), the table at `i` is body `i` calling the table. -/
theorem funcsFix_apply (sigs : List (Nat × Nat))
    (rs : HVector RegFn (sigs.map fun (n, m) => (⟨fnTys sigs ++ nats n⟩, nats m)))
    (hrs : RegsMono rs) (i : Nat) (xs : List Nat) :
    funcsFix (fun T => bodies sigs T sigs rs) i xs =
      bodies sigs (funcsFix fun T => bodies sigs T sigs rs) sigs rs i xs :=
  congrFun (congrFun (funcsFix_unfold (bodies_monotone sigs sigs rs hrs)) i) xs

end RegionCF
