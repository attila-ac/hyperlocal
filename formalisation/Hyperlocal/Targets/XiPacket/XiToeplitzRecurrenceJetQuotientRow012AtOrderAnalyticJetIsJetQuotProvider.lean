/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotProvider.lean

  Historical installer surface for quotient-jet facts of the three pivot windows.

  UPDATED POLICY:
  This file contains no axioms.
  The old payload names are now theorem-backed wrappers, and the installer
  instance is re-exported under the Route-A quotient-window equality provider.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetIsJetQuotFromRouteAJetEq

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

/--
Compatibility wrapper: theorem-backed `w0At` quotient-jet fact.
-/
theorem jet_w0At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3AtOrderQuot m s (TAC.z_w0At s) (w0At m s) := by
  exact TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_w0At (m := m) (s := s)

/--
Compatibility wrapper: theorem-backed `wp2At` quotient-jet fact.
-/
theorem jet_wp2At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3AtOrderQuot m s (TAC.z_wp2At s) (wp2At m s) := by
  exact TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp2At (m := m) (s := s)

/--
Compatibility wrapper: theorem-backed `wp3At` quotient-jet fact.
-/
theorem jet_wp3At_trueAnalytic_payload
    (m : ℕ) (s : OffSeed Xi)
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    IsJet3AtOrderQuot m s (TAC.z_wp3At s) (wp3At m s) := by
  exact TAC.XiJetWindowIsJetAtOrderQuotProvider.jet_wp3At (m := m) (s := s)

section
variable [TAC.XiJetWindowEqAtOrderQuotProvider]

/--
Compatibility installer under the Route-A quotient-window equality provider.
-/
instance : TAC.XiJetWindowIsJetAtOrderQuotProvider where
  jet_w0At := fun m s => jet_w0At_trueAnalytic_payload (m := m) (s := s)
  jet_wp2At := fun m s => jet_wp2At_trueAnalytic_payload (m := m) (s := s)
  jet_wp3At := fun m s => jet_wp3At_trueAnalytic_payload (m := m) (s := s)

end

end XiPacket
end Targets
end Hyperlocal
