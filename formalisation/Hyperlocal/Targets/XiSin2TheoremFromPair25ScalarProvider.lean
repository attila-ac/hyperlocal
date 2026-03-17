import Hyperlocal.Targets.XiPair25ResonantScalarProvider
import Hyperlocal.Targets.CriticalZero_Zeta_FinalLocalScalarTargetInterpolatedFromPair25Sigma2DeltaBCoeff5
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Derive the prime-2 resonant sine theorem from the bundled pair-{2,5} resonant
scalar provider.

This is not closed. It compresses the remaining seam from the two scalar facts
to the single one-prime sine theorem `h2_res`.
-/
theorem sin2_zero_on_resonant_branch_of_pair25_scalar_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiPair25ResonantScalarProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      Real.sin ((t s) * Real.log (2 : ℝ)) = 0 := by
  intro s hres
  exact
    (Hyperlocal.Targets.sin_log2_zero_on_resonant_branch_of_pair25_sigma2delta_bCoeff5
      (hσ2δ_res :=
        XiPair25ResonantScalarProvider.sigma2_eq_two_delta_on_resonant_branch_global)
      (hb5_res :=
        XiPair25ResonantScalarProvider.bCoeff5_zero_on_resonant_branch_global)
      (s := s))
    hres

#print axioms sin2_zero_on_resonant_branch_of_pair25_scalar_provider

end Targets
end Hyperlocal