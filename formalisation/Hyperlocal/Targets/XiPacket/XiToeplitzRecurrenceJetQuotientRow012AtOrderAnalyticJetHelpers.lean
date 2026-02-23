/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetHelpers.lean

  Purpose:
  Provide a small API layer so downstream bridge/instance files do NOT depend on the
  `XiJetQuotRow012AtOrder_AnalyticJet` structure fields.

  Downstream should depend only on:
  * theorem-level base Row012 bundle (from analytic upstream)
  * minimal axiom surface: window = xiJet3AtOrder
  * derived IsJet3AtOrder facts (by rewriting)
  * JetQuotShiftBridge3AtOrder instances (from the dedicated instances file)

  This makes later axiom→theorem replacement completely local.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderInstancesFromAnalyticExtractor

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

/-- Window equality axioms, re-exported as simp-friendly lemmas. -/
@[simp] theorem w0At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) :
    w0At m s = xiJet3AtOrder m (z_w0At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder

@[simp] theorem wp2At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) :
    wp2At m s = xiJet3AtOrder m (z_wp2At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder

@[simp] theorem wp3At_eq_xiJet3AtOrder (m : ℕ) (s : OffSeed Xi) :
    wp3At m s = xiJet3AtOrder m (z_wp3At s) :=
  (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder

/-- Derived jet fact for `w0At`, using only the window equality axiom. -/
theorem isJet3AtOrder_w0At (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_w0At s))

/-- Derived jet fact for `wp2At`, using only the window equality axiom. -/
theorem isJet3AtOrder_wp2At (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp2At s))

/-- Derived jet fact for `wp3At`, using only the window equality axiom. -/
theorem isJet3AtOrder_wp3At (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  simpa [IsJet3AtOrder] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp3At s))

/-- Packaged triple (handy for instance/bridge files). -/
theorem isJet3AtOrder_triple (m : ℕ) (s : OffSeed Xi) :
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
