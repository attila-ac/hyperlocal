import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpec
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcCoeff3RouteAStencil
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

variable [TAC.XiJetWindowEqAtOrderQuotProvider]
variable [RouteAWcScalarProvider]

/--
Parametric Route-A recurrence from an abstract row-0 `wc` frontier fact.

This theorem is the cycle-free algebraic core. It does not commit to where
the frontier fact came from.
-/
theorem routeA_recurrence_at_one_sub_rho_of_row0Frontier_wc
    (s : OffSeed Xi)
    (ht :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0) :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  have hsigma : row0Sigma s (wc s) = 0 := by
    rw [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)] at ht
    exact ht

  have hconv : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
    rw [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] at hsigma
    exact hsigma

  have hstencil :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
        = 0 := by
    rw [wc_convCoeff3_eq_routeA_stencil (s := s)] at hconv
    exact hconv

  have hs1 :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      -((JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)) := by
    apply eq_neg_of_add_eq_zero_right
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hstencil

  calc
    2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      -(((-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ))) := by
          ring
    _ =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
          rw [hs1]
          ring

/--
Wrapper using the current thin public seam.
-/
theorem routeA_recurrence_at_one_sub_rho_from_row0Frontier_wc
    (s : OffSeed Xi) :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  exact routeA_recurrence_at_one_sub_rho_of_row0Frontier_wc
    (s := s)
    (ht := xiJetQuot_row0_wc_spec (s := s))

end XiPacket
end Targets
end Hyperlocal
