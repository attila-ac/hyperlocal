/-
  Hyperlocal/Smoke.lean  (minimal + robust)

  Purpose:
  • Import only the concrete modules we need (no umbrella dependence).
  • #check the key API that the manuscript references.
  • No vector notation / extensionality / examples that can vary by repo.
-/

import Mathlib.Data.Complex.Basic
-- Factorisation & analytic layer
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.FactorizationGofSEntire
-- Growth & transcendence
import Hyperlocal.GrowthOrder
import Hyperlocal.Transcendence
import Hyperlocal.FactorizationConsequences
-- Cancellation / Instability
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Appendix.InstabilityK1
import Hyperlocal.Appendix.InstabilityK2
import Hyperlocal.Cancellation.WrapUp
import Hyperlocal.Cancellation.WrapUpExport

import Hyperlocal.Transport.TAC

#check Hyperlocal.Transport.TAC.oddPart_PhiPrime
#check Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
#check Hyperlocal.Transport.TAC.tac_finite_prime_witness_2_3
#check Hyperlocal.Transport.parityₗ_comp_TACToeplitzR



noncomputable section

-- =========================
-- #check suite (no runtime)
-- =========================

-- Growth / Subexp–poly finisher
#check Hyperlocal.GrowthOrder.Order1Bound
#check Hyperlocal.GrowthOrder.OrderLEOne
#check Hyperlocal.GrowthOrder.subExpPoly_eval_Rρk
#check Hyperlocal.GrowthOrder.order1_for_H_of_order1_for_G
#check Hyperlocal.GrowthOrder.Order1Bound.mul_of_subExpPoly'

-- Transcendence filter
#check Hyperlocal.Transcendence.IsPolynomialFun
#check Hyperlocal.Transcendence.Transcendental
#check Hyperlocal.Transcendence.transcendental_of_factor
#check Hyperlocal.Transcendence.G_transcendental_of_eval_poly_factor

-- Consequences interface (growth forward + transcendence back)
#check Hyperlocal.Consequences.orderLEOne_for_H_of_orderLEOne_for_G
#check Hyperlocal.Consequences.G_transcendental_of_RrhoK_factor

-- Factorisation analytic: G entire
#check Hyperlocal.FactorizationGofSEntire.entire_G_of_factorisation

-- Instability hook + wrappers
#check Hyperlocal.Cancellation.UnstableHom
#check Hyperlocal.Cancellation.BridgeData
#check Hyperlocal.Cancellation.no_cancellation_if_unstable
#check Hyperlocal.Appendix.InstabilityK1.unstable_k1_all_t
#check Hyperlocal.Appendix.InstabilityK2.unstable_k2_all_t




end section
