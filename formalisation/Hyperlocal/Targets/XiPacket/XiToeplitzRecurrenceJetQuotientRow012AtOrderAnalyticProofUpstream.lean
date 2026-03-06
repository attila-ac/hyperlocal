/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticProofUpstream.lean

  Upstream provider for the analytic Row012 target bundle.

  DAG contract:
  * This file may import only "true analytic" layers (factorisation / FE-RC / jet identities, etc.).
  * It MUST NOT import any Route–C landing/discharge modules, nor anything that depends on the
    analytic extractor stack.

  IMPORTANT (cycle + axiom hygiene):
  * This file MUST NOT import any provider *installers*.
  * It must depend only on provider *interfaces* via typeclass hypotheses.

  Reason:
  If this file imports an installer that installs an axiom-stub instance, the resulting
  upstream constants become permanently dependent on that axiom-stub.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderFromPropBridge

-- provider interfaces ONLY (no installers here)
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider

-- analytic upstream goal (already interface-parametric)
import Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrderAnalyticUpstream

-- algebraic bridges
import Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow012StencilGoalsAtOrderFromSigmaExtraLin
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012PropAtOrderFromStencilGoalsAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Derived upstream *stencil* convCoeff goals (pure algebra). -/
theorem xiRow012StencilGoalsAtOrder_analytic_upstream
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiRow012StencilGoalsAtOrder m s := by
  exact xiRow012StencilGoalsAtOrder_of_sigmaExtraLinGoals
    (m := m) (s := s)
    (xiRow012SigmaExtraLinGoalsAtOrder_analytic_upstream (m := m) (s := s))

/-- Derived upstream Prop-level Row012 payload (pure algebra). -/
theorem xiJetQuotRow012PropAtOrder_analytic_upstream
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRow012PropAtOrder m s := by
  classical
  exact xiJetQuotRow012PropAtOrder_of_stencilGoalsAtOrder
    (m := m) (s := s)
    (xiRow012StencilGoalsAtOrder_analytic_upstream (m := m) (s := s))

/-- Upstream analytic endpoint for the Type-valued Row012 target bundle (definitional from Prop). -/
noncomputable def xiJetQuotRow012AtOrder_analytic_upstream
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [XiAtOrderCoords01Provider] :
    XiJetQuotRow012AtOrder m s :=
  xiJetQuotRow012AtOrder_of_row012PropAtOrder (m := m) (s := s)
    (xiJetQuotRow012PropAtOrder_analytic_upstream (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
