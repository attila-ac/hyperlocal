/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Frontier.lean

  Legacy row-0 frontier exports (Route–B canonical windows).

  STATUS:
  * `xiJetQuot_row0_w0/wp2/wp3` are theorem-level by specializing the
    AtOrder frontier at `m = 0`.
  * `xiJetQuot_row0_wc` remains staged here (no AtOrder theorem in this snapshot).

  IMPORTANT (cycle-breaker):
  This file must remain cycle-safe: do NOT import Row0Concrete/Row0Analytic layers.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Transport.TACToeplitz
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpec

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- `w0At 0` is definitional `w0` (proved by simp only; no `Function.iterate`). -/
lemma w0At_zero (s : OffSeed Xi) : w0At 0 s = w0 s := by
  funext i
  -- Keep simp surface narrow: rely on your actual defs, but do NOT mention Function.iterate.
  simp [w0At, w0, xiTransportedJet, xiCentralJetAt, xiCentralJet, xiJet3At, cderivIter]

/-- `wp2At 0` is definitional `wp2` (simp-only). -/
lemma wp2At_zero (s : OffSeed Xi) : wp2At 0 s = wp2 s := by
  funext i
  simp [wp2At, wpAt, wp2, w0At_zero (s := s)]

/-- `wp3At 0` is definitional `wp3` (simp-only). -/
lemma wp3At_zero (s : OffSeed Xi) : wp3At 0 s = wp3 s := by
  funext i
  simp [wp3At, wpAt, wp3, w0At_zero (s := s)]

/-- Route–B frontier: Toeplitz row–0 annihilation for `w0` (derived). -/
theorem xiJetQuot_row0_w0 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa [w0At_zero (s := s)] using (xiJetQuot_row0_w0At (m := 0) (s := s))

/-- Historical name (was an axiom): now a theorem, sourced from the Row0-frontier spec. -/
theorem xiJetQuot_row0_wc (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 :=
by
  simpa using (xiJetQuot_row0_wc_spec (s := s))

/-- Route–B frontier: Toeplitz row–0 annihilation for `wp2` (derived). -/
theorem xiJetQuot_row0_wp2 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa [wp2At_zero (s := s)] using (xiJetQuot_row0_wp2At (m := 0) (s := s))

/-- Route–B frontier: Toeplitz row–0 annihilation for `wp3` (derived). -/
theorem xiJetQuot_row0_wp3 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa [wp3At_zero (s := s)] using (xiJetQuot_row0_wp3At (m := 0) (s := s))

namespace Row0FrontierExport
export _root_.Hyperlocal.Targets.XiPacket
  (xiJetQuot_row0_w0 xiJetQuot_row0_wc xiJetQuot_row0_wp2 xiJetQuot_row0_wp3)
end Row0FrontierExport

end XiPacket
end Targets
end Hyperlocal
