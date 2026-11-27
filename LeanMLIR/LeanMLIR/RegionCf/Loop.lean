/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCf.Mono
import LeanMLIR.RegionCf.Simp
import LeanMLIR.RegionCf.Arith

/-!
# A loop, as a region op

```
(n, a, b) := (n, 0, 1)
while {
  if n != 0 then continue (n - 1, b, a + b)
  else break (n, a, b)
}
return a
```

computes the `n`-th Fibonacci number.
-/

open Ctxt (Var Valuation)
open TyDenote (toType)

namespace RegionCfFunctor.Loop

open MLIR.AST (Region)

abbrev N : Ty Arith.Ty := .base .nat

/-- The loop body, on the state `(n, a, b)`: a flag (`0`: break) and the new state. -/
def bodyAst : Region 0 := [mlir_region| {
  ^bb0(%n : !nat, %a : !nat, %b : !nat):
    %f, %n', %a', %b' = "cf.ite"(%n, %n, %a, %b) ({
      ^bb0(%n : !nat, %a : !nat, %b : !nat):
        %one = "arith.cst"() {value = 1} : () -> (!nat)
        %m = "arith.sub"(%n, %one) : (!nat, !nat) -> (!nat)
        %s = "arith.add"(%a, %b) : (!nat, !nat) -> (!nat)
        "return"(%one, %m, %b, %s) : (!nat, !nat, !nat, !nat) -> ()
    }, {
      ^bb0(%n : !nat, %a : !nat, %b : !nat):
        %zero = "arith.cst"() {value = 0} : () -> (!nat)
        "return"(%zero, %n, %a, %b) : (!nat, !nat, !nat, !nat) -> ()
    }) : (!nat, !nat, !nat, !nat) -> (!nat, !nat, !nat, !nat)
    "return"(%f, %n', %a', %b') : (!nat, !nat, !nat, !nat) -> ()
}]

abbrev body := [cf_region| $(bodyAst)]

/-- `(n, a, b) := (n, 0, 1); while body; return a` -/
def prog := [cf| {
  ^bb0(%n : !nat):
    %c0 = "arith.cst"() {value = 0} : () -> (!nat)
    %c1 = "arith.cst"() {value = 1} : () -> (!nat)
    %n', %a, %b = "cf.while"(%n, %c0, %c1) ($(bodyAst)) : (!nat, !nat, !nat) -> (!nat, !nat, !nat)
    "return"(%a) : (!nat) -> ()
}]

/-! ## The specification -/

def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib n + fib (n + 1)

/-- `fib`, computed by the program. -/
def Fib' (n : Nat) : Option Nat :=
  (prog.denote (Valuation.ofHVector (.cons (n : Nat) .nil))).map fun r => (r.head : Nat)

#guard (List.range 12).all fun n => Fib' n == some (fib n)

/-! ## The proof

The body, run on a state, is one step (`cf_reduce`); the loop, by `whileLoop_unfold` and
induction on `n`, is `n` steps. -/

/-- The loop's step function, as `denote` gives it to `whileLoop`. -/
abbrev step (st : HVector toType [N, N, N]) : Option (Bool × HVector toType [N, N, N]) :=
  (body.denote (Valuation.ofHVector (rev st))).map fun r => (Base.isTrue (d := Arith) r.head, r.tail)

theorem step_eq (n a b : Nat) :
    step ((n : Nat) ::ₕ (a : Nat) ::ₕ (b : Nat) ::ₕ .nil) =
      if n = 0 then some (false, (n : Nat) ::ₕ (a : Nat) ::ₕ (b : Nat) ::ₕ .nil)
      else some (true, (n - 1 : Nat) ::ₕ (b : Nat) ::ₕ (a + b : Nat) ::ₕ .nil) := by
  unfold step body
  cases n with
  | zero => rfl
  | succ n => rfl

/-- `n` steps from `(a, b)`. -/
def iter : Nat → Nat → Nat → Nat
  | 0, a, _ => a
  | n + 1, a, b => iter n b (a + b)

/-- **The loop runs `n` steps**, then breaks. -/
theorem loop (n a b : Nat) :
    ∃ b' : Nat, whileLoop step ((n : Nat) ::ₕ (a : Nat) ::ₕ (b : Nat) ::ₕ .nil) =
      some ((0 : Nat) ::ₕ (iter n a b : Nat) ::ₕ b' ::ₕ .nil) := by
  induction n generalizing a b with
  | zero => exact ⟨b, by rw [whileLoop_unfold, step_eq]; rfl⟩
  | succ n ih =>
    obtain ⟨b', h⟩ := ih b (a + b)
    exact ⟨b', by rw [whileLoop_unfold, step_eq]; simpa [iter] using h⟩

theorem iter_fib (n k : Nat) : iter n (fib k) (fib (k + 1)) = fib (n + k) := by
  induction n generalizing k with
  | zero => simp [iter]
  | succ n ih =>
    rw [iter, show fib k + fib (k + 1) = fib (k + 2) from rfl, ih]
    congr 1; omega

/-- **The program computes `fib`.** -/
theorem Fib'_eq (n : Nat) : Fib' n = some (fib n) := by
  obtain ⟨b', h⟩ := loop n 0 1
  unfold Fib' prog
  cf_reduce
  -- `cf_reduce` leaves the loop's body as it is: `step`, so `loop` rewrites
  rw [h]
  cf_reduce
  have := iter_fib n 0
  simp only [fib, Nat.add_zero] at this
  rw [this]

/-! ## A loop that never stops

```
while { continue (n + 1) }
```

has no value (`Option`'s `none`), by `whileLoop_diverges`. -/

def spinAst : Region 0 := [mlir_region| {
  ^bb0(%n : !nat):
    %one = "arith.cst"() {value = 1} : () -> (!nat)
    %m = "arith.add"(%n, %one) : (!nat, !nat) -> (!nat)
    "return"(%one, %m) : (!nat, !nat) -> ()
}]

abbrev spinBody := [cf_region| $(spinAst)]

def spin := [cf| {
  ^bb0(%n : !nat):
    %r = "cf.while"(%n) ($(spinAst)) : (!nat) -> (!nat)
    "return"(%r) : (!nat) -> ()
}]

abbrev spinStep (st : HVector toType [N]) : Option (Bool × HVector toType [N]) :=
  (spinBody.denote (Valuation.ofHVector (rev st))).map fun r => (Base.isTrue (d := Arith) r.head, r.tail)

theorem spinStep_eq (n : Nat) :
    spinStep ((n : Nat) ::ₕ .nil) = some (true, (n + 1 : Nat) ::ₕ .nil) :=
  rfl

/-- **`spin` does not terminate.** -/
theorem spin_none (n : Nat) : spin.denote (Valuation.ofHVector ((n : Nat) ::ₕ .nil)) = none := by
  have h := whileLoop_diverges spinStep (fun _ => True)
    (by rintro (_ | ⟨(k : Nat), ⟨⟩⟩) -; exact ⟨_, spinStep_eq k, trivial⟩)
    ((n : Nat) ::ₕ .nil) trivial
  unfold spin
  cf_reduce
  rw [h]
  rfl

end RegionCfFunctor.Loop
