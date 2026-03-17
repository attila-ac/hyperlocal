import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Row0SigmaPair25
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

/--
Provider-free resonant closure of the scalar seam.

This is the direct payoff of the already-green pair-{2,5} resonant theorem
`W1.row0Sigma_wc_eq_zero_of_resonant32` combined with the closed form
`W1.row0Sigma_wc_closed`.

No `RouteAWcScalarProvider` is used here.
-/
theorem sigma2_eq_two_delta_of_resonant32
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [XiJetQuotRec2AtOrderTrueAnalyticPrime]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hres :
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0) :
    JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ) := by
  have hsigma : row0Sigma s (wc s) = 0 :=
    W1.row0Sigma_wc_eq_zero_of_resonant32 (s := s) (hres := hres)
  rw [W1.row0Sigma_wc_closed (s := s)] at hsigma
  exact sub_eq_zero.mp hsigma

/--
Provider-free form of the same seam in row-0 sigma language.
-/
theorem row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta_provider_free
    (s : OffSeed Xi)
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    row0Sigma s (wc s) = 0 := by
  rw [W1.row0Sigma_wc_closed (s := s), hσ2δ]
  ring

/--
Provider-free row-0 Toeplitz frontier consequence.

This is the exact above-cycle insertion point you want for downstream consumers.
-/
theorem toeplitz_row0_wc_eq_zero_of_sigma2_eq_two_delta_provider_free
    (s : OffSeed Xi)
    (hσ2δ : JetQuotOp.σ2 s = (2 : ℂ) * (XiTransport.delta s : ℂ)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  rw [toeplitzL_row0_eq_row0Sigma (s := s) (w := wc s)]
  exact row0Sigma_wc_eq_zero_of_sigma2_eq_two_delta_provider_free
    (s := s) hσ2δ

end XiPacket
end Targets
end Hyperlocal
