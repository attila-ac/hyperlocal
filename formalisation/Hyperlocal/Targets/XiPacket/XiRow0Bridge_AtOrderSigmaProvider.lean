/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProvider.lean

  DAG-clean interface: provide the three AtOrder row0Sigma vanishings for
  w0At/wp2At/wp3At.

  This isolates the dependency choice:
  * DAG-clean: axiom instance (for now)
  * optional non-cycle-safe: extractor/recurrence glue instance
  * future: true analytic proof instance
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Prop bundle: the three row0Sigma equalities at order `m` for the canonical AtOrder windows. -/
structure XiAtOrderSigmaOut (m : ℕ) (s : OffSeed Xi) : Prop where
  hw0AtSigma  : row0Sigma s (w0At m s)  = 0
  hwp2AtSigma : row0Sigma s (wp2At m s) = 0
  hwp3AtSigma : row0Sigma s (wp3At m s) = 0

/-- Provider of the sigma bundle. -/
class XiAtOrderSigmaProvider : Type where
  sigma : ∀ (m : ℕ) (s : OffSeed Xi), XiAtOrderSigmaOut m s

/-- Canonical accessor. -/
theorem xiAtOrderSigmaOut_provided
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    XiAtOrderSigmaOut m s :=
  XiAtOrderSigmaProvider.sigma (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
