/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyStencilToCoordEq.lean

  Consume the Row012 reverse-convolution stencil gate (n = 3,4,5) and expose
  explicit linear equalities on the window coordinates.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff345Algebra
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Hyperlocal.Cancellation

theorem coordEqs_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    row0Sigma s w = 0 ∧
    (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 ∧
    (-2 : ℂ) * (w 0) = 0 := by
  classical
  rcases H with ⟨G, hfac, hjet, h3, h4, h5⟩

  have hSigma : row0Sigma s w = 0 := by
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w)] using h3

  -- IMPORTANT: here `h4` / `h5` are already the *unfolded sum* form
  have h4' : (JetQuotOp.σ2 s) * (w 0) + (-2 : ℂ) * (w 1) = 0 := by
    simpa [convCoeff4_unfold_eq_lincomb (s := s) (w := w)] using h4

  have h5' : (-2 : ℂ) * (w 0) = 0 := by
    simpa [convCoeff5_unfold_eq_lincomb (s := s) (w := w)] using h5

  exact ⟨hSigma, h4', h5'⟩

theorem w0_eq_zero_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3)
    (H : Row012ConvolutionAtRev s z w) :
    w 0 = 0 := by
  classical
  have h : (-2 : ℂ) * (w 0) = 0 :=
    (coordEqs_of_row012ConvolutionAtRev (s := s) (z := z) (w := w) H).2.2
  have h' : (-2 : ℂ) ≠ 0 := by norm_num
  exact (mul_eq_zero.mp h).resolve_left h'

namespace CauchyStencilToCoordEqExport
export _root_.Hyperlocal.Targets.XiPacket
  (coordEqs_of_row012ConvolutionAtRev
   w0_eq_zero_of_row012ConvolutionAtRev)
end CauchyStencilToCoordEqExport

end XiPacket
end Targets
end Hyperlocal
