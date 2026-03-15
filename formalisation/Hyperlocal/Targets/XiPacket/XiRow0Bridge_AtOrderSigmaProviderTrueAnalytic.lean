/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderTrueAnalytic.lean

  "Sigma provider" for AtOrder windows.

  IMPORTANT:
  this file is a producer for `XiAtOrderSigmaProvider`, so it must not depend on
  any compatibility layer that already requires `[XiAtOrderSigmaProvider]`.

  Therefore we build the three sigma facts directly from the analytic concrete
  extract + scalar-goals pipeline, and then install the provider instance
  conditionally under the theorem-side assumptions actually needed by that
  analytic path.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderGateFromAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-!
## Sigma lemmas for the three canonical AtOrder windows

We use the analytic extract
  `xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic`
and then scalarize it via
  `scalarGoalsAtOrder_of_extract`.
-/

theorem sigma_w0At
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (w0At m s) = 0 := by
  let E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  let GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E
  exact GS.hw0At

theorem sigma_wp2At
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wp2At m s) = 0 := by
  let E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  let GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E
  exact GS.hwp2At

theorem sigma_wp3At
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    row0Sigma s (wp3At m s) = 0 := by
  let E : XiJetQuotRow0ConcreteExtractAtOrder m s :=
    xiJetQuotRow0ConcreteExtractAtOrder_fromAnalytic (m := m) (s := s)
  let GS : XiJetQuotRow0ScalarGoalsAtOrder m s :=
    scalarGoalsAtOrder_of_extract (m := m) (s := s) E
  exact GS.hwp3At

/-- Conditional provider instance from the analytic AtOrder route. -/
instance
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiAtOrderSigmaProvider where
  sigma m s :=
    { hw0AtSigma  := sigma_w0At  (m := m) (s := s)
      hwp2AtSigma := sigma_wp2At (m := m) (s := s)
      hwp3AtSigma := sigma_wp3At (m := m) (s := s) }

end XiPacket
end Targets
end Hyperlocal
