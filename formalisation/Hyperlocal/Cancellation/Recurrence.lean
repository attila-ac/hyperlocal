import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

open Finset
open scoped BigOperators

noncomputable section
namespace Hyperlocal
namespace Cancellation

/-- Coefficient accessor (just an alias so `simp [coeff]` normalizes). -/
@[simp] def coeff (f : ℕ → ℂ) (n : ℕ) : ℂ := f n

/-- Cauchy product coefficient at index `n`. -/
def convCoeff (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  (range (n+1)).sum (fun i => coeff a i * coeff b (n - i))

/-- `(F·G)^∧(n) = ∑_{i=0}^n F^∧(i) G^∧(n-i)` — by definition. -/
@[simp] lemma coeff_product (a b : ℕ → ℂ) (n : ℕ) :
    convCoeff a b n = (range (n+1)).sum (fun i => a i * b (n - i)) := rfl

/-- “The convolution matches `h` at every index”. -/
def Convolution (a b h : ℕ → ℂ) : Prop :=
  ∀ n, convCoeff a b n = h n

/-- Isolate the pivot `a k * b m` from the Cauchy sum at `m+k`. -/
lemma recurrence_coeff_k
    {a b h : ℕ → ℂ} {m k : ℕ}
    (H : Convolution a b h) :
    a k * b m
      = - ((range (m + k + 1)).erase k).sum (fun i => a i * b (m + k - i))
        + h (m + k) := by
  classical
  -- Expand convolution at m+k
  have Hmk : (range (m + k + 1)).sum (fun i => a i * b (m + k - i)) = h (m + k) := by
    have := H (m + k)
    simp [coeff_product] at this
    exact this
  -- k ∈ range (m+k+1)
  have hk : k ∈ range (m + k + 1) := by
    have : k ≤ m + k := Nat.le_add_left _ _
    simpa [mem_range, Nat.lt_succ_iff] using this
  -- Split off i = k
  have split :
      ((range (m + k + 1)).erase k).sum (fun i => a i * b (m + k - i))
        + (a k * b (m + k - k))
      = (range (m + k + 1)).sum (fun i => a i * b (m + k - i)) :=
    Finset.sum_erase_add (s := range (m + k + 1)) (a := k)
      (f := fun i => a i * b (m + k - i)) hk
  -- Move the erase-sum to the RHS using subtraction
  have step₁ :
      a k * b (m + k - k)
        = (range (m + k + 1)).sum (fun i => a i * b (m + k - i))
          - ((range (m + k + 1)).erase k).sum (fun i => a i * b (m + k - i)) := by
    -- subtract the erase-sum on both sides; (S_erase + term) - S_erase = term
    have := congrArg
      (fun z => z - ((range (m + k + 1)).erase k).sum (fun i => a i * b (m + k - i)))
      split
    -- LHS simplifies via `add_sub_cancel`
    simpa [add_sub_cancel] using this
  -- simplify m+k-k = m, and rewrite `-S + F` as `F - S`
  have step₂ :
      a k * b m
        = - ((range (m + k + 1)).erase k).sum (fun i => a i * b (m + k - i))
          + (range (m + k + 1)).sum (fun i => a i * b (m + k - i)) := by
    simpa [Nat.add_sub_cancel, sub_eq_add_neg, add_comm] using step₁
  -- replace the full sum by h (m+k)
  simpa [Hmk] using step₂

/-! ### Smokes -/

/-- Convolution with δ₀ (Dirac at 0) returns `b`. -/
example (b : ℕ → ℂ) :
    let a : ℕ → ℂ := fun i => if i = 0 then 1 else 0
    let h : ℕ → ℂ := b
    Convolution a b h := by
  intro a h n
  classical
  -- `0 ∈ range (n+1)`
  have h0 : 0 ∈ range (n+1) := by
    simpa [mem_range, Nat.lt_succ_iff]
  -- Split off the `i = 0` term.
  have split :
      ((range (n+1)).erase 0).sum (fun i => (if i = 0 then 1 else 0) * b (n - i))
        + ((if 0 = 0 then 1 else 0) * b (n - 0))
      = (range (n+1)).sum (fun i => (if i = 0 then 1 else 0) * b (n - i)) :=
    Finset.sum_erase_add (s := range (n+1)) (a := 0)
      (f := fun i => (if i = 0 then 1 else 0) * b (n - i)) h0
  -- Everything except `i = 0` vanishes.
  have vanish :
      ((range (n+1)).erase 0).sum (fun i => (if i = 0 then 1 else 0) * b (n - i)) = 0 := by
    refine Finset.sum_eq_zero ?term
    intro i hi
    have hne : i ≠ 0 := (Finset.mem_erase.mp hi).1
    simp [hne]
  -- The whole sum is `b n`.
  have sum_eq :
      (range (n+1)).sum (fun i => (if i = 0 then 1 else 0) * b (n - i)) = b n := by
    -- use the split, rewriting the erase-sum to 0 and n-0 = n
    simpa [vanish, Nat.sub_self] using split.symm
  -- Goal: `convCoeff a b n = h n`
  change convCoeff a b n = h n
  -- Expand LHS, then use `sum_eq`; RHS is `b n` since `h = b`.
  simp [coeff_product, a, h, sum_eq]

end Cancellation
end Hyperlocal
