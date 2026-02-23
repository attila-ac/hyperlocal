/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetQuotShiftBridgeInstancesFromAnalyticExtractor.lean

  Refactor (name-robust):
  * Do NOT depend on the `XiJetQuotRow012AtOrder_AnalyticJet` structure fields.
  * Do NOT depend on helper lemma names (avoids namespace/import brittleness).
  * Depend only on:
      - theorem-level analytic upstream base (elsewhere)
      - minimal axiom surface: `xiJetWindowEqAtOrder`
      - canonical theorem: `isJet3AtOrder_xiJet3AtOrder`
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetAxiom

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

theorem isJet3AtOrder_w0At_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) := by
  -- window equality is the only axiom surface
  have hw :
      w0At m s = xiJet3AtOrder m (z_w0At s) :=
    (xiJetWindowEqAtOrder (m := m) (s := s)).w0At_eq_xiJet3AtOrder
  -- derive jet fact by rewriting to canonical jet window
  simpa [IsJet3AtOrder, hw] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_w0At s))

theorem isJet3AtOrder_wp2At_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) := by
  have hw :
      wp2At m s = xiJet3AtOrder m (z_wp2At s) :=
    (xiJetWindowEqAtOrder (m := m) (s := s)).wp2At_eq_xiJet3AtOrder
  simpa [IsJet3AtOrder, hw] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp2At s))

theorem isJet3AtOrder_wp3At_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  have hw :
      wp3At m s = xiJet3AtOrder m (z_wp3At s) :=
    (xiJetWindowEqAtOrder (m := m) (s := s)).wp3At_eq_xiJet3AtOrder
  simpa [IsJet3AtOrder, hw] using
    (isJet3AtOrder_xiJet3AtOrder (m := m) (z := z_wp3At s))

theorem isJet3AtOrder_triple_fromAnalyticExtractor
    (m : ℕ) (s : OffSeed Xi) :
    IsJet3AtOrder m (z_w0At s) (w0At m s) ∧
    IsJet3AtOrder m (z_wp2At s) (wp2At m s) ∧
    IsJet3AtOrder m (z_wp3At s) (wp3At m s) := by
  refine ⟨?_, ?_, ?_⟩
  · exact isJet3AtOrder_w0At_fromAnalyticExtractor (m := m) (s := s)
  · exact isJet3AtOrder_wp2At_fromAnalyticExtractor (m := m) (s := s)
  · exact isJet3AtOrder_wp3At_fromAnalyticExtractor (m := m) (s := s)

end TAC

end XiPacket
end Targets
end Hyperlocal
