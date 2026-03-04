/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierSpec.lean

  Axiom-thin interface for the single Row0 frontier fact at `wc`.

  Policy:
  * MUST NOT import any sigma/coords01 provider axioms.
  * MUST NOT route through analytic extractor spines.
  * Only states the minimal Toeplitz row0 vanishing fact at `wc`.

  IMPORTANT:
  Name is suffixed `_spec` to avoid collisions with legacy frontier modules.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Transport.TACToeplitz

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Row0 frontier fact at `wc`: Toeplitz row0 vanishes (spec-layer). -/
axiom xiJetQuot_row0_wc_spec
  (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
