/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_WcCoeff3RouteAStencil.lean

  Local theorem-side reduction for the remaining `wc` coeff-3 seam.

  Purpose:
  * reduce
        convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0
    to the Route-A scalar stencil

        (-2) G''(1-ρ) + σ2 G'(1-ρ) - σ3 G(1-ρ)

  for G = routeA_G s.

  The clean theorem `wc_convCoeff3_clean` is obtained once that stencil
  is proven to vanish.
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

/--
Rewrite the wc coeff-3 convolution as the exact Route-A scalar stencil.
-/
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
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) := by
            change (-2 : ℂ) * (wc s (2 : Fin 3))
              + (JetQuotOp.σ2 s) * (wc s (1 : Fin 3))
              - (JetQuotOp.σ3 s) * (wc s (0 : Fin 3))
              =
              (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
                + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
                - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ)
            rw [← JetQuotOp.routeA_G_wc_coord2 (s := s),
                ← JetQuotOp.routeA_G_wc_coord1 (s := s),
                ← JetQuotOp.routeA_G_wc_coord0 (s := s)]
/--
Bridge lemma: if the Route-A stencil vanishes, then the coeff-3
convolution vanishes.
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

/--
Clean coeff-3 theorem once the Route-A stencil vanishing is available.
-/
theorem wc_convCoeff3_clean
    (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hStencil :
      (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
        + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
        - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 :=
  wc_convCoeff3_clean_of_routeA_stencil s hStencil

end XiPacket
end Targets
end Hyperlocal
