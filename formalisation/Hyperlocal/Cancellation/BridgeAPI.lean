/-
  Hyperlocal/Cancellation/BridgeAPI.lean

  Collision-free API shim: packaged recurrence records + constructors
  on top of the core lemmas from `Bridge.lean`.  Uses distinct names
  to avoid clashing with any existing `PivotRecurrence` you may have.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Basic
import Hyperlocal.Cancellation.Bridge

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace BridgeAPI

open Hyperlocal.Cancellation.Bridge
open Finset

/-- Packaged “pivot recurrence at k” (API shim, distinct name). -/
structure PivotRecSpec (R G H : ℕ → ℂ) (k : ℕ) : Prop where
  Rk_ne : R k ≠ 0
  recurrence :
    ∀ m, G m =
      ( H (m + k)
        - ((range (m + k + 1)).erase k).sum
            (fun i => R i * G (m + k - i)) ) / (R k)

/-- Packaged “windowed pivot recurrence at k with bound L” (API shim). -/
structure WindowedPivotRecSpec (R G H : ℕ → ℂ) (k L : ℕ) : Prop where
  Rk_ne : R k ≠ 0
  recurrence :
    ∀ m, L ≤ m + k →
      G m =
        ( H (m + k)
          - ((range (L+1)).erase k).sum
              (fun i => R i * G (m + k - i)) ) / (R k)

/-- Constructor from a convolution identity. -/
lemma mkPivotSpec
    {R G H : ℕ → ℂ} {k : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0) :
    PivotRecSpec R G H k :=
by
  refine ⟨hRk, ?_⟩
  intro m
  simpa using
    recurrence_of_convolution_pivot
      (R := R) (G := G) (H := H) (k := k) hconv hRk m

/-- Constructor (windowed) from convolution + window hypothesis. -/
lemma mkWindowedSpec
    {R G H : ℕ → ℂ} {k L : ℕ}
    (hconv : Hyperlocal.Cancellation.Convolution R G H)
    (hRk   : R k ≠ 0)
    (hwin  : WindowUpTo R L) :
    WindowedPivotRecSpec R G H k L :=
by
  refine ⟨hRk, ?_⟩
  intro m hLm
  simpa using
    recurrence_of_convolution_window_le
      (R := R) (G := G) (H := H) (k := k) (L := L) hconv hRk hwin m hLm

end BridgeAPI
end Cancellation
end Hyperlocal
end section
