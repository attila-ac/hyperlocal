/-
  Hyperlocal/Targets/XiPacket/XiLemmaC_Semantic_FromRecurrence.lean

  Endpoint: build XiLemmaC_Semantic from the recurrence frontier.
-/

import Hyperlocal.Targets.XiPacket.XiWindowLemmaC_FromRecurrence
import Hyperlocal.Targets.XiPacket.XiLemmaC_SemanticToWindowPayload
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

theorem xiLemmaC_Semantic_fromRecurrence (s : Hyperlocal.OffSeed Xi) :
    XiLemmaC_Semantic s := by
  -- get the 3 scalar facts from the “Lemma C” bundle
  have hC : XiLemmaC s := xiWindowLemmaC_fromRecurrence (s := s)
  -- package them into the semantic record
  exact ⟨hC.hell2, hC.hell3, hC.hkappa⟩

end XiPacket
end Targets
end Hyperlocal
