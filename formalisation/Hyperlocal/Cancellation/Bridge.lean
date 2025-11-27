/-
  Cancellation/Bridge.lean (uppercase manuscript notation)
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

From `Convolution R G H` (i.e. coefficients satisfy `H = R * G`)
and a pivot slot with `R k ≠ 0`, we can solve the Cauchy identity at
level `m + k` for `G m`:

G m =
( H (m + k)
  - ∑ i in (range (m + k + 1)).erase k, R i * G (m + k - i) ) / (R k).

This is a direct rearrangement of `Hyperlocal.Cancellation.recurrence_coeff_k`.
-/
lemma recurrence_of_convolution_pivot
    {R G H : ℕ → ℂ} {k : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0) :
    ∀ m : ℕ,
      G m
        = ( H (m + k)
            - ((range (m + k + 1)).erase k).sum
                (fun i => R i * G (m + k - i)) ) / (R k) := by
  classical
  intro m
  -- Name the non-pivot sum for clarity.
  let S : ℂ :=
    ((range (m + k + 1)).erase k).sum (fun i => R i * G (m + k - i))
  -- Cauchy pivot identity from your file:
  --   R k * G m = -S + H (m+k) = H (m+k) - S
  have base :=
    Hyperlocal.Cancellation.recurrence_coeff_k
      (a := R) (b := G) (h := H) (m := m) (k := k) hconv
  have base' : R k * G m = H (m + k) - S := by
    simpa [S, sub_eq_add_neg, add_comm] using base
  -- Divide by R k (nonzero) to isolate G m.
  have : G m = (H (m + k) - S) / (R k) := by
    refine (eq_div_iff_mul_eq hRk).2 ?_
    -- We need: (G m) * (R k) = H (m+k) - S; commute factors to use `base'`.
    simpa [mul_comm] using base'
  simpa [S] using this


/-- Window hypothesis: coefficients of `R` vanish past `L`. -/
def WindowUpTo (R : ℕ → ℂ) (L : ℕ) : Prop :=
  ∀ i, L < i → R i = 0

/-
This is the pivot recurrence at level `m+k`, with the Cauchy sum truncated
to `i ≤ L`. Terms with `i > L` vanish by the window hypothesis.
The inclusion `(range (L+1)) ⊆ (range (m+k+1))` follows from `L ≤ m+k`.
-/
lemma recurrence_of_convolution_window_le
    {R G H : ℕ → ℂ} {k L : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0)
    (hwin  : WindowUpTo R L) :
    ∀ m : ℕ, L ≤ m + k →
      G m
        = ( H (m + k)
            - ((range (L+1)).erase k).sum
                (fun i => R i * G (m + k - i)) ) / (R k) := by
  classical
  intro m hLm
  -- start from the full pivot recurrence (uppercase names)
  have base :=
    Hyperlocal.Cancellation.Bridge.recurrence_of_convolution_pivot
      (R := R) (G := G) (H := H) (k := k) hconv hRk m

  -- big/small index sets and the summand
  let sBig   : Finset ℕ := (range (m + k + 1)).erase k
  let sSmall : Finset ℕ := (range (L + 1)).erase k
  let f : ℕ → ℂ := fun i => R i * G (m + k - i)

  -- (range (L+1)) ⊆ (range (m+k+1)) from L ≤ m+k; erase preserves inclusion
  have hsubset_range : range (L + 1) ⊆ range (m + k + 1) := by
    intro i hi
    have hi_le_L : i ≤ L := Nat.le_of_lt_succ (by simpa [Finset.mem_range] using hi)
    have hi_le_mk : i ≤ m + k := le_trans hi_le_L hLm
    simpa [Finset.mem_range] using Nat.lt_succ_of_le hi_le_mk
  have hsubset : sSmall ⊆ sBig := by
    intro i hiSmall
    rcases Finset.mem_erase.mp hiSmall with ⟨hik, hiRangeL⟩
    exact Finset.mem_erase.mpr ⟨hik, hsubset_range hiRangeL⟩

  -- outside sSmall, the summand vanishes (window kills R i when i > L)
  have hzero_outside :
      ∀ i ∈ sBig, i ∉ sSmall → f i = 0 := by
    intro i hiBig hiNotSmall
    rcases Finset.mem_erase.mp hiBig with ⟨hik, _hiRangeMK⟩
    have not_in_small_range : i ∉ range (L + 1) := by
      intro h; exact hiNotSmall (Finset.mem_erase.mpr ⟨hik, h⟩)
    have hi_gt_L : L < i := by
      by_contra hle
      have hi_le_L : i ≤ L := le_of_not_gt hle
      have : i ∈ range (L + 1) := by
        simpa [Finset.mem_range] using Nat.lt_succ_of_le hi_le_L
      exact not_in_small_range this
    have : R i = 0 := hwin i hi_gt_L
    simp [f, this]

  -- replace the big sum by the truncated sum (note: `sum_subset` expects `sSmall ⊆ sBig`)
  have sum_truncate : sBig.sum f = sSmall.sum f :=
    (Finset.sum_subset hsubset hzero_outside).symm

  simpa [sBig, sSmall, f, sum_truncate] using base

/-! ### Packaged APIs for instability consumers (matches manuscript notation) -/
namespace API

/-- Manuscript notation aliases. -/
abbrev R := ℕ → ℂ
abbrev G := ℕ → ℂ
abbrev H := ℕ → ℂ

/--
`PivotRecurrence R G H k` says: the pivot slot `R k` is nonzero and
we have the explicit order-`k` pivot recurrence for **all** `m`.
-/
structure PivotRecurrence (R G H : ℕ → ℂ) (k : ℕ) : Prop where
  rk_ne : R k ≠ 0
  step  :
    ∀ m : ℕ,
      G m
        = ( H (m + k)
            - ((range (m + k + 1)).erase k).sum
                (fun i => R i * G (m + k - i)) ) / (R k)

/-- Build a `PivotRecurrence` from a convolution identity and `R k ≠ 0`. -/
lemma mk_pivot
    {R G H : ℕ → ℂ} {k : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0) :
    PivotRecurrence R G H k := by
  refine ⟨hRk, ?step⟩
  intro m
  simpa using
    Hyperlocal.Cancellation.Bridge.recurrence_of_convolution_pivot
      (R := R) (G := G) (H := H) (k := k) hconv hRk m

/-- Window hypothesis (uppercase alias). -/
def WindowUpTo (R : ℕ → ℂ) (L : ℕ) : Prop :=
  Hyperlocal.Cancellation.Bridge.WindowUpTo R L

/--
`WindowedPivotRecurrence R G H k L` packages the truncated recurrence under a window `L`.
-/
structure WindowedPivotRecurrence (R G H : ℕ → ℂ) (k L : ℕ) : Prop where
  rk_ne : R k ≠ 0
  hkL   : k ≤ L
  stepL :
    ∀ ⦃m : ℕ⦄, L ≤ m + k →
      G m
        = ( H (m + k)
            - ((range (L + 1)).erase k).sum
                (fun i => R i * G (m + k - i)) ) / (R k)

/-- Build a `WindowedPivotRecurrence` from convolution + window + pivot in range. -/
lemma mk_windowed
    {R G H : ℕ → ℂ} {k L : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0)
    (hwin  : WindowUpTo R L)
    (hkL   : k ≤ L) :
    WindowedPivotRecurrence R G H k L := by
  refine ⟨hRk, hkL, ?step⟩
  intro m hLm
  simpa using
    Hyperlocal.Cancellation.Bridge.recurrence_of_convolution_window_le
      (R := R) (G := G) (H := H) (k := k) (L := L)
      hconv hRk hwin m hLm

end API

end Bridge
end Cancellation
end Hyperlocal
