/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Concrete.lean

  Concrete row-0 Toeplitz annihilation facts (Route–B canonical windows),
  packaged in a way that is SAFE to import from upstream proof modules.

  CRITICAL:
  * This file MUST NOT import:
      - XiToeplitzRecurrenceJetQuotientRow0Frontier
      - XiToeplitzRecurrenceJetQuotientRow0FrontierSpecTheorem
    because those sit on the “frontier export” side and will create cycles.

  UPDATED POLICY:
  * `w0/wp2/wp3` are now derived from the theorem-side AtOrder spec proofs at `m = 0`.
  * `wc` is currently still obtained from the historical Spec surface.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpecProofUpstream
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

theorem xiJetQuot_row0_w0 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0 := by
  simpa [w0At_zero (s := s)] using (xiJetQuot_row0_w0At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wc (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0 := by
  simpa using (xiJetQuot_row0_wc_spec (s := s))

theorem xiJetQuot_row0_wp2 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0 := by
  simpa [wp2At_zero (s := s)] using (xiJetQuot_row0_wp2At_spec_proof (m := 0) (s := s))

theorem xiJetQuot_row0_wp3 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0 := by
  simpa [wp3At_zero (s := s)] using (xiJetQuot_row0_wp3At_spec_proof (m := 0) (s := s))

end XiPacket
end Targets
end Hyperlocal
