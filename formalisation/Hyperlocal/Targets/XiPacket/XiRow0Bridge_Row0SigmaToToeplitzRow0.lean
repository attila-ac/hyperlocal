/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0SigmaToToeplitzRow0.lean

  Cycle-safe algebra bridge:

    row0Sigma s w = 0  ⇒  (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0:Fin 3) = 0.

  This is the row-0 analogue of `XiRow0Bridge_Row0SigmaShiftToToeplitzRow12.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
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

/-- Toeplitz row-0 vanishing from `row0Sigma` vanishing on the base window. -/
theorem toeplitz_row0_eq_zero_of_row0Sigma_eq_zero
    (s : OffSeed Xi) (w : Window 3)
    (h : row0Sigma s w = 0) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  classical

  -- `row0Sigma` is the same linear form as Toeplitz row-0, up to commutativity.
  have hlin :
      (-JetQuotOp.σ3 s) * (w (0 : Fin 3))
        + (JetQuotOp.σ2 s) * (w (1 : Fin 3))
        + (-2 : ℂ) * (w (2 : Fin 3)) = 0 := by
    -- reorder the `row0Sigma` expression into the `w0,w1,w2` order
    have : (-(2 : ℂ)) * (w (2 : Fin 3))
              + (JetQuotOp.σ2 s) * (w (1 : Fin 3))
              + (-(JetQuotOp.σ3 s)) * (w (0 : Fin 3)) = 0 := by
      simpa [row0Sigma] using h
    -- commutativity/associativity to match Toeplitz normal form
    simpa [add_assoc, add_left_comm, add_comm] using this

  have htoe :
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3)
        = ((-JetQuotOp.σ3 s) * w 0 + (JetQuotOp.σ2 s) * w 1) + (-2 : ℂ) * w 2 := by
    -- `toeplitzL_two_apply_fin0` gives coeff0*w0 + coeff1*w1 + coeff2*w2,
    -- and `simp` evaluates `aRk1` through `aR` + `σ1_eq_two`.
    simp [toeplitzL_two_apply_fin0, JetQuotOp.aRk1, JetQuotOp.aR, JetQuotOp.σ1_eq_two,
      add_assoc, add_left_comm, add_comm]

  have hlin' : ((-JetQuotOp.σ3 s) * w 0 + (JetQuotOp.σ2 s) * w 1) + (-2 : ℂ) * w 2 = 0 := by
    simpa [add_assoc] using hlin
  simpa [htoe] using hlin'

namespace Row0SigmaToToeplitzRow0Export
export _root_.Hyperlocal.Targets.XiPacket (toeplitz_row0_eq_zero_of_row0Sigma_eq_zero)
end Row0SigmaToToeplitzRow0Export

end XiPacket
end Targets
end Hyperlocal
