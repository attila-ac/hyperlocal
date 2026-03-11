import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyConvolutionDischarge
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

/--
Sharpened Route-A recurrence at `1 - ρ`, derived from the historical
`row0Sigma_wc_eq_zero` theorem.
-/
theorem routeA_recurrence_at_one_sub_rho_from_row0Sigma_wc
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
      2 * deriv (deriv (routeA_G s)) (1 - s.ρ)
        =
      (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        -
      (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  have hsigma : row0Sigma s (wc s) = 0 :=
    row0Sigma_wc_eq_zero (s := s)

  have hconv : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wc s)] using hsigma

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

end XiPacket
end Targets
end Hyperlocal
