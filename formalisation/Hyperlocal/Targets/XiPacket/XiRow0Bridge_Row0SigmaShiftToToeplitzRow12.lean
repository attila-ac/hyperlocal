/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0SigmaShiftToToeplitzRow12.lean

  Pure algebra bridge:

    row0Sigma s (shiftWin1 w) = 0  ⇒  toeplitz row-1 equation for w
    row0Sigma s (shiftWin2 w) = 0  ⇒  toeplitz row-2 equation for w

  IMPORTANT FIX (your diagnosis is right):
  Use `JetQuotOp.aRk1` (the Window-3 truncation `j ↦ aR (j+1)`), not `JetQuotOp.aR`.
  Using `aR` directly shifts indices and turns “row-1” into the “row-2-like” equation.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WindowShiftRow0Sigma
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceToeplitzLToRow3
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open ToeplitzLToRow3

/--
Row-1 Toeplitz vanishing from `row0Sigma` vanishing on the 1-shifted window.

`row0Sigma_shiftWin1` computes:
  row0Sigma s (shiftWin1 w) = σ2*s*w2 + (-σ3*s)*w1

Toeplitz row-1 for `toeplitzL 2 (aRk1 s) w` is:
  (aRk1 s 0) * w1 + (aRk1 s 1) * w2 = 0
and by definitions:
  aRk1 s 0 = aR s 1 = -σ3 s
  aRk1 s 1 = aR s 2 =  σ2 s
so the expressions match (up to commutativity of addition).
-/
theorem toeplitz_row1_eq_zero_of_row0Sigma_shiftWin1_eq_zero
    (s : OffSeed Xi) (w : Window 3)
    (h : row0Sigma s (shiftWin1 w) = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 := by
  classical

  -- turn the hypothesis into the explicit coordinate linear form
  have hlin :
      (JetQuotOp.σ2 s) * (w (2 : Fin 3)) + (-JetQuotOp.σ3 s) * (w (1 : Fin 3)) = 0 := by
    simpa [row0Sigma_shiftWin1 (s := s) (w := w)] using h

  -- reorder to match the toeplitz normal form ordering
  have hlin' :
      (-JetQuotOp.σ3 s) * (w (1 : Fin 3)) + (JetQuotOp.σ2 s) * (w (2 : Fin 3)) = 0 := by
    simpa [add_comm, add_left_comm, add_assoc] using hlin

  -- compute Toeplitz row-1 with the correct coefficient truncation `aRk1`
  have htoe :
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3)
        = (-JetQuotOp.σ3 s) * (w (1 : Fin 3)) + (JetQuotOp.σ2 s) * (w (2 : Fin 3)) := by
    -- `toeplitzL_two_apply_fin1` gives `coeffs 0 * w1 + coeffs 1 * w2`
    -- and `simp` evaluates `aRk1 s 0` / `aRk1 s 1` via `aR`.
    simp [toeplitzL_two_apply_fin1, JetQuotOp.aRk1, JetQuotOp.aR,
          add_comm, add_left_comm, add_assoc]

  -- finish without `simp` (avoid any `mul_eq_zero` rewriting into a disjunction)
  rw [htoe]
  exact hlin'

/--
Row-2 Toeplitz vanishing from `row0Sigma` vanishing on the 2-shifted window.

`row0Sigma_shiftWin2` computes:
  row0Sigma s (shiftWin2 w) = (-σ3*s)*w2

Toeplitz row-2 for `toeplitzL 2 (aRk1 s) w` is:
  (aRk1 s 0) * w2 = 0
and `aRk1 s 0 = -σ3 s`.
-/
theorem toeplitz_row2_eq_zero_of_row0Sigma_shiftWin2_eq_zero
    (s : OffSeed Xi) (w : Window 3)
    (h : row0Sigma s (shiftWin2 w) = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 := by
  classical

  have hlin : (-JetQuotOp.σ3 s) * (w (2 : Fin 3)) = 0 := by
    simpa [row0Sigma_shiftWin2 (s := s) (w := w)] using h

  have htoe :
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3)
        = (-JetQuotOp.σ3 s) * (w (2 : Fin 3)) := by
    -- `toeplitzL_two_apply_fin2` gives `coeffs 0 * w2`
    simp [toeplitzL_two_apply_fin2, JetQuotOp.aRk1, JetQuotOp.aR]

  -- finish by rewriting, not by `simpa` (again, avoid `mul_eq_zero` simp)
  rw [htoe]
  exact hlin

/-! ### Re-export -/
namespace Row0SigmaShiftToToeplitzRow12Export
export _root_.Hyperlocal.Targets.XiPacket
  (toeplitz_row1_eq_zero_of_row0Sigma_shiftWin1_eq_zero
   toeplitz_row2_eq_zero_of_row0Sigma_shiftWin2_eq_zero)
end Row0SigmaShiftToToeplitzRow12Export

end XiPacket
end Targets
end Hyperlocal
