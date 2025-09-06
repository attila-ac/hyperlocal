-- formalisation/Hyperlocal/Cancellation/Recurrence.lean
import Mathlib.Data.Complex.Basic

/-!
# Linear recurrences for the `b`-sequence (no big-operators import)

We model a homogeneous part of order `L` with coefficients `a 1, …, a L`
(and a "leading" scalar `a0` multiplying `b n`) and an inhomogeneous term `h n`.

The intended manuscript shape is (for n ≥ L):
  a0 * b n = - ∑_{j=1..L} a j * b (n - j) + h n

We avoid `∑` notation (which needs `BigOperators`) and define a tiny recursive
finite-sum directly.
-/

-- Minimal finite-sum API (no BigOperators needed)
noncomputable section
open Nat

variable {α : Type*} [AddCommMonoid α]

/-- Sum f(0) + f(1) + ... + f(n-1). -/
def sumUpTo (n : ℕ) (f : ℕ → α) : α :=
  Nat.rec (0 : α) (fun k acc => acc + f k) n

@[simp] lemma sumUpTo_zero (f : ℕ → α) : sumUpTo 0 f = 0 := rfl
@[simp] lemma sumUpTo_succ (n : ℕ) (f : ℕ → α) :
    sumUpTo (n+1) f = sumUpTo n f + f n := rfl

lemma sumUpTo_const_zero (n : ℕ) :
    sumUpTo n (fun _ => (0 : α)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [sumUpTo_succ, ih]

lemma sumUpTo_map_mul_right {R} [Semiring R] {f : ℕ → R} (c : R) (n : ℕ) :
    sumUpTo n (fun k => c * f k) = c * sumUpTo n f := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp [sumUpTo_succ, ih, mul_add, mul_comm, mul_left_comm, mul_assoc]


noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

/-- Complex sequences indexed by natural numbers. -/
abbrev CSeq := ℕ → ℂ

/-- Simple finite sum `∑_{k=0}^{n-1} f k`, defined by primitive recursion. -/
def sumUpTo (n : ℕ) (f : ℕ → ℂ) : ℂ :=
  Nat.rec (0 : ℂ) (fun k acc => acc + f k) n

@[simp] lemma sumUpTo_zero (f : ℕ → ℂ) : sumUpTo 0 f = 0 := rfl

@[simp] lemma sumUpTo_succ (n : ℕ) (f : ℕ → ℂ) :
    sumUpTo (n+1) f = sumUpTo n f + f n := rfl

/-- Shifted finite sum `∑_{j=lo}^{hi-1} f j` as `sumUpTo (hi-lo)` over `j = lo + k`. -/
def sumRange (lo hi : ℕ) (f : ℕ → ℂ) : ℂ :=
  sumUpTo (hi - lo) (fun k => f (lo + k))

/-!
We package the recurrence data in a tiny record:

* `L` is the order (how many past terms enter).
* `a0` is the leading scalar multiplying `b n`.
* `a j` for `1 ≤ j ≤ L` are the shift-coefficients multiplying `b (n - j)`.
  (Outside this range `a j` may be anything; we only ever use `j ∈ {1,…,L}`.)
-/
structure RecSpec where
  L  : ℕ
  a0 : ℂ
  a  : ℕ → ℂ

namespace RecSpec

variable (R : RecSpec)

/-- Homogeneous right-hand side `- ∑_{j=1..L} a j * b (n - j)` without big-operator notation. -/
def homRHS (b : CSeq) (n : ℕ) : ℂ :=
  - sumRange 1 (R.L + 1) (fun j => R.a j * b (n - j))

/-- Full right-hand side: homogeneous part plus inhomogeneous term `h n`. -/
def fullRHS (h b : CSeq) (n : ℕ) : ℂ :=
  R.homRHS b n + h n

/--
The recurrence holds from a threshold `n0` if for all `n ≥ n0` we have
`a0 * b n = fullRHS h b n`.
-/
def HoldsFrom (h b : CSeq) (n0 : ℕ) : Prop :=
  ∀ n, n ≥ n0 → R.a0 * b n = R.fullRHS h b n

/-- By default we care from `n ≥ L` (so the shifts `n - j` never underflow). -/
abbrev Holds (h b : CSeq) : Prop := R.HoldsFrom h b R.L

end RecSpec

/-- Handy zero sequence. -/
@[simp] def zeroSeq : CSeq := fun _ => (0 : ℂ)

@[simp] lemma zeroSeq_eval (n : ℕ) : zeroSeq n = (0 : ℂ) := rfl

/-! ### Tiny smoke examples (compile-time sanity) -/

/-- Simple finite sum `∑_{k=0}^{n-1} f k`, defined by primitive recursion. -/
def sumUpTo (n : ℕ) (f : ℕ → ℂ) : ℂ :=
  Nat.rec (0 : ℂ) (fun k acc => acc + f k) n

@[simp] lemma sumUpTo_zero (f : ℕ → ℂ) : sumUpTo 0 f = 0 := rfl
@[simp] lemma sumUpTo_succ (n : ℕ) (f : ℕ → ℂ) :
    sumUpTo (n+1) f = sumUpTo n f + f n := rfl

/-- Shifted finite sum `∑_{j=lo}^{hi-1} f j` as `sumUpTo (hi-lo)` over `j = lo + k`. -/
def sumRange (lo hi : ℕ) (f : ℕ → ℂ) : ℂ :=
  sumUpTo (hi - lo) (fun k => f (lo + k))

/-- Sums of the zero function vanish. -/
@[simp] lemma sumUpTo_zero_fun (n : ℕ) : sumUpTo n (fun _ => (0 : ℂ)) = 0 := by
  induction n with
  | zero => simp
  | succ n ih => simpa [sumUpTo_succ, ih]

@[simp] lemma sumRange_zero_fun (lo hi : ℕ) :
    sumRange lo hi (fun _ => (0 : ℂ)) = 0 := by
  unfold sumRange
  simpa using (sumUpTo_zero_fun (n := hi - lo))

/-! ### Tiny smoke examples (compile-time sanity) -/

section Smokes

/-- A toy first-order recurrence with all coefficients zero is satisfied by the zero sequence. -/
example :
    (let R : RecSpec := ⟨1, (0 : ℂ), fun _ => (0 : ℂ)⟩;
     R.Holds (zeroSeq) (zeroSeq)) := by
  -- Evaluate the `let` so `simp` can see concrete fields.
  change (⟨1, (0 : ℂ), fun _ => (0 : ℂ)⟩ : RecSpec).Holds (zeroSeq) (zeroSeq)
  dsimp [RecSpec.Holds, RecSpec.HoldsFrom, RecSpec.fullRHS, RecSpec.homRHS,
         zeroSeq, sumRange]
  intro n hn
  -- Show the summand is literally the zero function.
  have hfun :
      (fun k => (⟨1, (0:ℂ), fun _ => (0:ℂ)⟩ : RecSpec).a (1 + k) *
                 (zeroSeq (n - (1 + k)))) = (fun _ => (0 : ℂ)) := by
    funext k; simp
  -- Now it's just 0 = -0 + 0.
  simp [hfun]

/-- With `a0 = 0` and `a = 0`, any `b` satisfies the recurrence with zero inhomogeneity. -/
example (b : CSeq) :
    (let R : RecSpec := ⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩;
     R.Holds (zeroSeq) b) := by
  change (⟨2, (0 : ℂ), fun _ => (0 : ℂ)⟩ : RecSpec).Holds (zeroSeq) b
  dsimp [RecSpec.Holds, RecSpec.HoldsFrom, RecSpec.fullRHS, RecSpec.homRHS,
         zeroSeq, sumRange]
  intro n hn
  -- Summand is zero because all `a j = 0`.
  have hfun :
      (fun k => (⟨2, (0:ℂ), fun _ => (0:ℂ)⟩ : RecSpec).a (1 + k) *
                 b (n - (1 + k))) = (fun _ => (0 : ℂ)) := by
    funext k; simp
  simp [hfun]

end Smokes


end Cancellation
end Hyperlocal
