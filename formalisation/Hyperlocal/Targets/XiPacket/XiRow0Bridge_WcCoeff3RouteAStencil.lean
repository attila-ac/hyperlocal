/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcCoeff3RouteAStencil.lean

  Local theorem-side reduction for the remaining `wc` coeff-3 seam.

  Purpose:
  * do NOT claim the final clean `wc` coeff-3 vanishing yet
  * do reduce the target
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0
    to the exact Route-A scalar stencil at `z = 1 - s.ρ`

  This isolates the real missing theorem:
      (-2) * G''(1-ρ) + σ2 * G'(1-ρ) - σ3 * G(1-ρ) = 0
  for `G = routeA_G s`.

  That is the honest next proof obligation.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Algebra
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetWindowEqFromRouteA_Theorem

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Cancellation
open Hyperlocal.Transport

theorem wc_convCoeff3_eq_routeA_stencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3
      =
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
  calc
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3
        =
        (-2 : ℂ) * (wc s ⟨2, by decide⟩)
          + (JetQuotOp.σ2 s) * (wc s ⟨1, by decide⟩)
          - (JetQuotOp.σ3 s) * (wc s ⟨0, by decide⟩) := by
            simpa using convCoeff3_eq_lincomb (s := s) (w := wc s)
    _ =
        (-2 : ℂ) * ((jet3 (routeA_G s) (1 - s.ρ)) ⟨2, by decide⟩)
          + (JetQuotOp.σ2 s) * ((jet3 (routeA_G s) (1 - s.ρ)) ⟨1, by decide⟩)
          - (JetQuotOp.σ3 s) * ((jet3 (routeA_G s) (1 - s.ρ)) ⟨0, by decide⟩) := by
            simpa [wc_eq_jet3_routeA (s := s)]
    _ =
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
            simp [jet3]

/--
If you later prove the Route-A scalar stencil vanishes at `z = 1 - s.ρ`,
this immediately yields the clean coeff-3 `wc` theorem.
-/
theorem wc_convCoeff3_clean_of_routeA_stencil
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hStencil :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 := by
  rw [wc_convCoeff3_eq_routeA_stencil (s := s)]
  exact hStencil

end XiPacket
end Targets
end Hyperlocal
