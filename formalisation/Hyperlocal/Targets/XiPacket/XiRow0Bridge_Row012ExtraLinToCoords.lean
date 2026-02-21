/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinToCoords.lean

  Pure algebra, cycle-safe:

  `Row012ExtraLin s w` is the pair of linear constraints
    h4 : (σ2 s)*w0 + (-2)*w1 = 0
    h5 : (-2)*w0 = 0.

  Over ℂ, these immediately imply the coordinate vanishings w0 = 0 and w1 = 0.
  Conversely, w0 = 0 and w1 = 0 imply Row012ExtraLin.

  This reduces the remaining “analytic” obligation: it suffices to prove
  `w 0 = 0` and `w 1 = 0` for each AtOrder window.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- `(-2 : ℂ) ≠ 0` helper. -/
lemma neg_two_ne_zero : (-2 : ℂ) ≠ 0 := by
  norm_num

/-- From `Row012ExtraLin`, extract `w 0 = 0`. -/
theorem row012ExtraLin_w0_eq_zero
    (s : OffSeed Xi) (w : Window 3) (HL : Row012ExtraLin s w) :
    w 0 = 0 := by
  have h : (-2 : ℂ) * (w 0) = 0 := HL.h5
  -- avoid simp turning this into a disjunction automatically
  have hz : (-2 : ℂ) = 0 ∨ w 0 = 0 := mul_eq_zero.mp h
  cases hz with
  | inl hbad => exact (False.elim (neg_two_ne_zero hbad))
  | inr hw0  => exact hw0

/-- From `Row012ExtraLin`, extract `w 1 = 0`. -/
theorem row012ExtraLin_w1_eq_zero
    (s : OffSeed Xi) (w : Window 3) (HL : Row012ExtraLin s w) :
    w 1 = 0 := by
  have hw0 : w 0 = 0 := row012ExtraLin_w0_eq_zero (s := s) (w := w) HL
  have h4 : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 := HL.h4
  -- kill the σ2*w0 term using hw0
  have h4' : (-2 : ℂ) * (w 1) = 0 := by
    simpa [hw0] using h4
  have hz : (-2 : ℂ) = 0 ∨ w 1 = 0 := mul_eq_zero.mp h4'
  cases hz with
  | inl hbad => exact (False.elim (neg_two_ne_zero hbad))
  | inr hw1  => exact hw1

/-- If `w 0 = 0` and `w 1 = 0` then `Row012ExtraLin s w`. -/
theorem row012ExtraLin_of_coords
    (s : OffSeed Xi) (w : Window 3)
    (hw0 : w 0 = 0) (hw1 : w 1 = 0) :
    Row012ExtraLin s w := by
  refine ⟨?_, ?_⟩
  · -- h4
    simp [hw0, hw1]
  · -- h5
    simp [hw0]

/-- Equivalence packaging: `Row012ExtraLin` ↔ `(w0=0 ∧ w1=0)`. -/
theorem row012ExtraLin_iff_coords
    (s : OffSeed Xi) (w : Window 3) :
    Row012ExtraLin s w ↔ (w 0 = 0 ∧ w 1 = 0) := by
  constructor
  · intro HL
    exact ⟨row012ExtraLin_w0_eq_zero (s := s) (w := w) HL,
           row012ExtraLin_w1_eq_zero (s := s) (w := w) HL⟩
  · rintro ⟨hw0, hw1⟩
    exact row012ExtraLin_of_coords (s := s) (w := w) hw0 hw1

end XiPacket
end Targets
end Hyperlocal
