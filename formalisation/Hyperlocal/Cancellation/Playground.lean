import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic   -- sum lemmas over Finset
import Mathlib.Algebra.BigOperators.Ring.Finset           -- mul_sum / sum_mul, etc.

open Finset
noncomputable section
namespace Playground

-- Sums of zero are zero.
example (n : ℕ) :
    (range n).sum (fun _ => (0 : ℂ)) = 0 := by
  classical
  -- fully qualified lemma to dodge notation/binder issues
  simpa using (Finset.sum_const_zero : (range n).sum (fun _ => (0 : ℂ)) = 0)

-- Sum of a constant over range n is n • c.
example (n : ℕ) (c : ℂ) :
    (range n).sum (fun _ => c) = n • c := by
  classical
  -- sum_const gives card • c, and card (range n) = n
  simpa [Finset.card_range] using
    (Finset.sum_const (s := range n) (b := c))

-- Range-succ decomposition.
example (n : ℕ) (f : ℕ → ℂ) :
    (range (n+1)).sum f = (range n).sum f + f n := by
  classical
  simpa using (Finset.sum_range_succ (f := f) (n := n))

-- Pull out a constant factor from under the sum.
example (n : ℕ) (c : ℂ) (f : ℕ → ℂ) :
    (range n).sum (fun k => c * f k)
      = c * (range n).sum (fun k => f k) := by
  classical
  -- mul_sum: c * (∑ f) = ∑ (c * f)   (flip sides)
  simpa using
    (Finset.mul_sum (s := range n) (f := fun k => f k) (a := c)).symm

end Playground
