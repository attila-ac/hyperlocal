import Hyperlocal.Targets.XiNoOffSeedDirectFromScalarSeam
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Conclusion.OffSeedToTAC
open Hyperlocal.Targets.XiPacket

/--
Direct Xi-side final export from the actual remaining local Route-A scalar theorem.
-/
theorem noOffSeed_Xi_final_of_routeA_scalar_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Xi := by
  exact noOffSeed_Xi_of_routeA_scalar
    (hroute := hroute)

/-- Direct ζ-side final export from the same local theorem. -/
theorem noOffSeed_Zeta_final_of_routeA_scalar_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0) :
    NoOffSeed Hyperlocal.zeta := by
  exact noOffSeed_Zeta_of_routeA_scalar
    (hroute := hroute)

/-- Direct RH-facing final export from the same local theorem. -/
theorem criticalzero_zeta_final_of_routeA_scalar_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hroute :
      ∀ s : Hyperlocal.OffSeed Xi,
        (-2 : ℂ) * deriv (deriv (routeA_G s)) (1 - s.ρ)
          + (JetQuotOp.σ2 s) * deriv (routeA_G s) (1 - s.ρ)
          - (JetQuotOp.σ3 s) * (routeA_G s) (1 - s.ρ) = 0)
    {ρ : ℂ}
    (hζ : Hyperlocal.zeta ρ = 0)
    (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  exact criticalzero_zeta_of_routeA_scalar
    (hroute := hroute)
    (hζ := hζ)
    (hIm := hIm)

#print axioms noOffSeed_Xi_final_of_routeA_scalar_closed
#print axioms noOffSeed_Zeta_final_of_routeA_scalar_closed
#print axioms criticalzero_zeta_final_of_routeA_scalar_closed

end Targets
end Hyperlocal
