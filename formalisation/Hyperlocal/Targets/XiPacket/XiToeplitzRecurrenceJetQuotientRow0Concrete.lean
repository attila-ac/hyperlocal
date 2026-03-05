/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

  Concrete row-0 Toeplitz annihilation facts (Route–B canonical windows),
  packaged in a way that is SAFE to import from upstream proof modules.

  CRITICAL:
  * This file MUST NOT import:
      - XiToeplitzRecurrenceJetQuotientRow0Frontier
      - XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem
    because those sit on the “frontier export” side and will create cycles.

  Policy:
  * `w0/wp2/wp3` are derived from the AtOrder frontier at `m = 0`.
  * `wc` is currently obtained from the historical Spec surface (still an axiom
    in this snapshot). This is what you later reclaim once the theorem migration
    is complete.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrder
import Hyperlocal.Transport.TACToeplitz

-- historical surface for `wc` (still axiom-thin in this snapshot)
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierSpec

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- `w0At 0` is definitional `w0` (simp-only; no `Function.iterate`). -/
lemma w0At_zero (s : OffSeed Xi) : w0At 0 s = w0 s := by
  funext i
  simp [w0At, w0, xiTransportedJet, xiCentralJetAt, xiCentralJet, xiJet3At, cderivIter]

/-- `wp2At 0` is definitional `wp2` (simp-only). -/
lemma wp2At_zero (s : OffSeed Xi) : wp2At 0 s = wp2 s := by
  funext i
  simp [wp2At, wpAt, wp2, w0At_zero (s := s)]

/-- `wp3At 0` is definitional `wp3` (simp-only). -/
lemma wp3At_zero (s : OffSeed Xi) : wp3At 0 s = wp3 s := by
  funext i
  simp [wp3At, wpAt, wp3, w0At_zero (s := s)]

/-- Concrete row0 fact for `w0` (derived from AtOrder at `m=0`). -/
theorem xiJetQuot_row0_w0 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa [w0At_zero (s := s)] using (xiJetQuot_row0_w0At (m := 0) (s := s))

/-- Concrete row0 fact for `wc` (currently via the historical spec surface). -/
theorem xiJetQuot_row0_wc (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_wc_spec (s := s))

/-- Concrete row0 fact for `wp2` (derived from AtOrder at `m=0`). -/
theorem xiJetQuot_row0_wp2 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa [wp2At_zero (s := s)] using (xiJetQuot_row0_wp2At (m := 0) (s := s))

/-- Concrete row0 fact for `wp3` (derived from AtOrder at `m=0`). -/
theorem xiJetQuot_row0_wp3 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa [wp3At_zero (s := s)] using (xiJetQuot_row0_wp3At (m := 0) (s := s))

end XiPacket
end Targets
end Hyperlocal
