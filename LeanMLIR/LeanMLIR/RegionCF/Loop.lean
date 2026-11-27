/-
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanMLIR.RegionCF.MutualRec

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

namespace RegionCF.Loop

open MutualRec (Com E v N)

/-- The loop body, on the state `(n, a, b)`: a flag (`0`: break) and the new state. -/
def body : Com ⟨[N, N, N]⟩ [N, N, N, N] :=
  .var (E (.ite [N, N, N] [N, N, N, N]) (.cons (v 0) (.cons (v 0) (.cons (v 1) (.cons (v 2) .nil))))
    (.cons
      -- n ≠ 0: continue with (n - 1, b, a + b)
      (.var (E (.cst 1) .nil) <|                                      -- one, n, a, b
       .var (E .sub (.cons (v 1) (.cons (v 0) .nil))) <|              -- m, one, n, a, b
       .var (E .add (.cons (v 3) (.cons (v 4) .nil))) <|              -- s, m, one, n, a, b
       .rets (.cons (v 2) (.cons (v 1) (.cons (v 5) (.cons (v 0) .nil)))))
      (.cons
        -- n = 0: break
        (.var (E (.cst 0) .nil) <|                                    -- zero, n, a, b
         .rets (.cons (v 0) (.cons (v 1) (.cons (v 2) (.cons (v 3) .nil)))))
        .nil))) <|
  .rets (.cons (v 0) (.cons (v 1) (.cons (v 2) (.cons (v 3) .nil))))

/-- `(n, a, b) := (n, 0, 1); while body; return a` -/
def prog : Com ⟨[N]⟩ [N] :=
  .var (E (.cst 0) .nil) <|                                           -- c0, n
  .var (E (.cst 1) .nil) <|                                           -- c1, c0, n
  .var (E (.while [N, N, N]) (.cons (v 2) (.cons (v 1) (.cons (v 0) .nil)))
    (.cons body .nil)) <|                                             -- n', a, b, c1, c0, n
  .rets (.cons (v 1) .nil)

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
abbrev step (st : HVector toType [N, N, N]) : Option (Nat × HVector toType [N, N, N]) :=
  (body.denote (Valuation.ofHVector st)).map fun r => (r.head, r.tail)

theorem step_eq (n a b : Nat) :
    step ((n : Nat) ::ₕ (a : Nat) ::ₕ (b : Nat) ::ₕ .nil) =
      if n = 0 then some (0, (n : Nat) ::ₕ (a : Nat) ::ₕ (b : Nat) ::ₕ .nil)
      else some (1, (n - 1 : Nat) ::ₕ (b : Nat) ::ₕ (a + b : Nat) ::ₕ .nil) := by
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
  -- `cf_reduce` ran the loop's body as far as it goes; it is still `step`, up to unfolding
  erw [h]
  cf_reduce
  have := iter_fib n 0
  simp only [fib, Nat.add_zero] at this
  rw [this]

end RegionCF.Loop
