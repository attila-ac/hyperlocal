/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetHelpers.lean

  Step 4 refactor:
  This helper layer now depends on the explicit provider `[XiJetWindowEqAtOrderProvider]`,
  not on a hidden global axiom installer.

  NOTE:
  This file is for the *order* arm (`IsJet3AtOrder` / `xiJet3AtOrder`), so it should not
  import quotient-bridge instance layers.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

namespace TAC

open Hyperlocal.Targets.XiTransport

/-- Theorem-level Row012 bundle (already provided by the analytic upstream proof). -/
noncomputable def xiJetQuotRow012AtOrder_base
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s :=
  Hyperlocal.Targets.XiPacket.xiJetQuotRow012AtOrder_analytic_upstream (m := m) (s := s)

/-- Window equality axioms, re-exported as simp-friendly lemmas (provider-based). -/
@[simp] theorem w0At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    w0At m s = xiJet3AtOrder m (z_w0At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder

@[simp] theorem wp2At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    wp2At m s = xiJet3AtOrder m (z_wp2At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder

@[simp] theorem wp3At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    wp3At m s = xiJet3AtOrder m (z_wp3At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder

/-- Derived jet fact for `w0At`, using only the window equality provider. -/
theorem isJet3AtOrder_w0At (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_w0At s))

/-- Derived jet fact for `wp2At`, using only the window equality provider. -/
theorem isJet3AtOrder_wp2At (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp2At s))

/-- Derived jet fact for `wp3At`, using only the window equality provider. -/
theorem isJet3AtOrder_wp3At (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp3At s))

/-- Packaged triple (handy for instance/bridge files). -/
theorem isJet3AtOrder_triple (m : ℕ) (s : OffSeed Xi) [XiJetWindowEqAtOrderProvider] :
    IsJet3AtOrder m (z_w0At s) (w0At m s) ∧
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) ∧
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  refine ⟨isJet3AtOrder_w0At (m := m) (s := s),
          isJet3AtOrder_wp2At (m := m) (s := s),
          isJet3AtOrder_wp3At (m := m) (s := s)⟩

end TAC

end XiPacket
end Targets
end Hyperlocal
