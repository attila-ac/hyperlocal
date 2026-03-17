import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Hyperlocal.Transport.PrimeTrigPacket
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
Split pair-{2,5} scalar surface collapses directly to the missing local wp5 theorem.
-/
theorem wp5_row0_zero_on_resonant_branch_of_pair25_scalars
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ))
    (hb5_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        Hyperlocal.Transport.PrimeTrigPacket.bCoeff (σ s) (t s) (5 : ℝ) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  intro s hres
  exact XiPacket.W1.row0Sigma_wpAt5_eq_zero_of_sigma2_eq_two_delta_and_bCoeff5_zero
    (s := s)
    (hσ2δ := hσ2δ_res s hres)
    (hb5 := hb5_res s hres)

#print axioms wp5_row0_zero_on_resonant_branch_of_pair25_scalars

end Targets
end Hyperlocal
