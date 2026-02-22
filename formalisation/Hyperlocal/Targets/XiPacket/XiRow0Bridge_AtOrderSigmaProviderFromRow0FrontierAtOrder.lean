/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderFromRow0FrontierAtOrder.lean

  Extractor-free glue: derive the sigma provider instance at order `m` from the
  existing Route–B AtOrder Row0 frontier projections:

    xiJetQuot_row0_w0At/wp2At/wp3At :
      (toeplitzL 2 (JetQuotOp.aRk1 s) (w?At m s)) (0 : Fin 3) = 0

  Then rewrite row-0 ToeplitzL into row0Sigma using
    toeplitzL_row0_eq_row0Sigma.

  IMPORTANT:
  * This file is NOT "true analytic": it depends on the Row0 concrete frontier
    (which may still be axiomatic today).
  * It is, however, extractor-free and DAG-safe.
  * It is intended as an intermediate burden-reduction step:
      sigma goals become definitional from the existing single Row0 frontier cliff.

  Usage:
  * If you import this file, you no longer need XiRow0Bridge_AtOrderSigmaProviderAxiom.
  * Upstream Row012 analytic provider SHOULD STILL NOT import this (it would violate
    the "true analytic only" contract). Use it in non-analytic glue layers or tests.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteProof

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Sigma bundle at order derived from the Route–B frontier projections. -/
theorem xiAtOrderSigmaOut_fromRow0FrontierAtOrder
    (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · -- w0At
    have ht : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
      xiJetQuot_row0_w0At (m := m) (s := s)
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)
    simpa [hrew] using ht
  · -- wp2At
    have ht : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
      xiJetQuot_row0_wp2At (m := m) (s := s)
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)
    simpa [hrew] using ht
  · -- wp3At
    have ht : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
      xiJetQuot_row0_wp3At (m := m) (s := s)
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)
    simpa [hrew] using ht

/-- Provider instance derived from the existing Row0 frontier (extractor-free). -/
instance : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromRow0FrontierAtOrder

end XiPacket
end Targets
end Hyperlocal
