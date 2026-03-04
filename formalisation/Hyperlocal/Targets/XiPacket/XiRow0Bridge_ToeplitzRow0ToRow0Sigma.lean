/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_ToeplitzRow0ToRow0Sigma.lean

  Cycle-safe algebra bridge:

    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0:Fin 3) = 0  ⇒  row0Sigma s w = 0.

  This is the converse direction of `XiRow0Bridge_Row0SigmaToToeplitzRow0.lean`.

  Motivation:
  Some glue layers (e.g. sigma-provider installers) obtain row-0 annihilation
  as a Toeplitz statement and need to restate it in the `row0Sigma` normal form
  without importing the heavier Row0 concrete proof stack.
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

/-- `row0Sigma` vanishes if Toeplitz row-0 vanishes (pure rewriting). -/
theorem row0Sigma_eq_zero_of_toeplitz_row0_eq_zero
    (s : OffSeed Xi) (w : Window 3)
    (h : (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0) :
    row0Sigma s w = 0 := by
  classical

  -- Expand Toeplitz row-0 into the explicit 3-term linear form.
  have htoe :
      (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3)
        = ((-JetQuotOp.σ3 s) * w 0 + (JetQuotOp.σ2 s) * w 1) + (-2 : ℂ) * w 2 := by
    simp [toeplitzL_two_apply_fin0, JetQuotOp.aRk1, JetQuotOp.aR, JetQuotOp.σ1_eq_two,
      add_assoc]

  have hlin : ((-JetQuotOp.σ3 s) * w 0 + (JetQuotOp.σ2 s) * w 1) + (-2 : ℂ) * w 2 = 0 := by
    simpa [htoe] using h

  -- Reorder the same expression into the `row0Sigma` orientation.
  -- `row0Sigma s w = (-2)*w2 + σ2*w1 + (-σ3)*w0`.
  have hlin' : (-(2 : ℂ)) * (w (2 : Fin 3))
      + (JetQuotOp.σ2 s : ℂ) * (w (1 : Fin 3))
      + (-(JetQuotOp.σ3 s : ℂ)) * (w (0 : Fin 3)) = 0 := by
    -- first flatten to `(-σ3)*w0 + σ2*w1 + (-2)*w2 = 0`
    have : (-JetQuotOp.σ3 s) * (w (0 : Fin 3))
          + (JetQuotOp.σ2 s) * (w (1 : Fin 3))
          + (-2 : ℂ) * (w (2 : Fin 3)) = 0 := by
      -- `hlin` has `((a*b0 + b*b1) + c*b2) = 0`.
      simpa [add_assoc, add_left_comm, add_comm] using hlin
    -- now reorder into the `w2,w1,w0` orientation.
    simpa [add_assoc, add_left_comm, add_comm] using this

  simpa [row0Sigma] using hlin'

namespace ToeplitzRow0ToRow0SigmaExport
export _root_.Hyperlocal.Targets.XiPacket (row0Sigma_eq_zero_of_toeplitz_row0_eq_zero)
end ToeplitzRow0ToRow0SigmaExport

end XiPacket
end Targets
end Hyperlocal
