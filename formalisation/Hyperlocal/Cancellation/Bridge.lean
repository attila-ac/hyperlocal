/-
  Cancellation/Bridge.lean (minimal stub)
  Bridge from H = R * G (at the coefficient level) to a pivot recurrence for G.
  This version avoids index-window tricks and Jet/instability dependencies.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

import Hyperlocal.Cancellation.Recurrence   -- coeff, convCoeff, Convolution, recurrence_coeff_k

open Finset
open scoped BigOperators

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace Bridge

/--
**Pivot recurrence (no window).**

From `Convolution r g h` (i.e. coefficients satisfy `H = R * G`)
and a pivot slot with `r k ≠ 0`, we can solve the Cauchy identity at
level `m + k` for `g m`:

g m =
( h (m + k)

∑ i in (range (m + k + 1)).erase k, r i * g (m + k - i) ) / (r k).

pgsql
Copy code

This is a direct rearrangement of `Hyperlocal.Cancellation.recurrence_coeff_k`.
-/
lemma recurrence_of_convolution_pivot
    {r g h : ℕ → ℂ} {k : ℕ}
    (H : Hyperlocal.Cancellation.Convolution r g h)
    (rk_ne : r k ≠ 0) :
    ∀ m : ℕ,
      g m
        = ( h (m + k)
            - ((range (m + k + 1)).erase k).sum
                (fun i => r i * g (m + k - i)) ) / (r k) := by
  classical
  intro m
  -- Name the non-pivot sum for clarity.
  let S : ℂ :=
    ((range (m + k + 1)).erase k).sum (fun i => r i * g (m + k - i))
  -- Cauchy pivot identity from your file:
  --   r k * g m = -S + h (m+k) = h (m+k) - S
  have base :=
    Hyperlocal.Cancellation.recurrence_coeff_k
      (a := r) (b := g) (h := h) (m := m) (k := k) H
  have base' : r k * g m = h (m + k) - S := by
    simpa [S, sub_eq_add_neg, add_comm] using base
  -- Divide by r k (nonzero) to isolate g m.
  -- Use `eq_div_iff_mul_eq`: a = b / c ↔ a * c = b.
  have : g m = (h (m + k) - S) / (r k) := by
    refine (eq_div_iff_mul_eq rk_ne).2 ?_
    -- We need: (g m) * (r k) = h (m+k) - S; commute factors to use `base'`.
    simpa [mul_comm] using base'
  simpa [S] using this

end Bridge
end Cancellation
end Hyperlocal
