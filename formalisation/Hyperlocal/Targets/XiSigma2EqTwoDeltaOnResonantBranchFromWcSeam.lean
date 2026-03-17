import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_WcSigma2DeltaToToeplitzRow0Core
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

theorem sigma2_eq_two_delta_on_resonant_branch_of_row0Sigma_wc_zero
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hsigma_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        row0Sigma s (wc s) = 0) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  intro s hres
  have hs : row0Sigma s (wc s) = 0 := hsigma_res s hres
  have hclosed :
      row0Sigma s (wc s)
        =
      (JetQuotOp.σ2 s : ℂ) - (2 : ℂ) * (XiTransport.delta s : ℂ) := by
    simpa using (XiPacket.W1.row0Sigma_wc_closed (s := s))
  rw [hclosed] at hs
  exact sub_eq_zero.mp hs

theorem row0Sigma_wc_zero_on_resonant_branch_of_sigma2_eq_two_delta
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hσ2δ_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 := by
  intro s hres
  exact row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta
    (s := s)
    (hσ2δ := hσ2δ_res s hres)

#print axioms sigma2_eq_two_delta_on_resonant_branch_of_row0Sigma_wc_zero
#print axioms row0Sigma_wc_zero_on_resonant_branch_of_sigma2_eq_two_delta

end Targets
end Hyperlocal
