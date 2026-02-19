/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3PayloadAtOrderFromFrontier.lean

  DOWNSTREAM CONVERGENCE PROOF:

  Proves the Route–C AtOrder convCoeff(n=3) payload from the Route–B frontier
  extractor facts.

  IMPORTANT:
  This file MUST NOT be imported by the upstream recurrence/discharge chain,
  otherwise it recreates the AtOrderRecurrence↔Frontier dependency cycle.

  Intended use:
  * Keep this file as the proof object.
  * Later, when the AtOrder DAG is rearranged (or when you can safely flip the
    dependency direction), you can replace `xiRow0Coeff3AtOrderPayload_axiom`
    by this theorem without importing frontier back upstream.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3PayloadAtOrder
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3ExtractorAtOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Cancellation

/-- The payload proved from the frontier extractor (theorem-level, downstream). -/
theorem xiRow0Coeff3AtOrderPayload_fromFrontier (m : ℕ) (s : OffSeed Xi) :
    XiRow0Coeff3AtOrderPayload m s := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using (row0ConvCoeff3_w0At (m := m) (s := s))
  · simpa using (row0ConvCoeff3_wp2At (m := m) (s := s))
  · simpa using (row0ConvCoeff3_wp3At (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
