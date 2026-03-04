/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpec.lean

  Axiom-thin interface for the Row0 frontier-at-order facts used downstream.

  Policy:
  * MUST NOT import any sigma/coords01 provider axioms.
  * MUST NOT route through analytic extractor spines.
  * Only states the minimal Row0 Toeplitz-row0 vanishing facts at the three window points.
-/

import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Transport.TACToeplitz

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Row0 frontier fact at `w0At`: Toeplitz row0 vanishes. -/
axiom xiJetQuot_row0_w0At
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0

/-- Row0 frontier fact at `wp2At`: Toeplitz row0 vanishes. -/
axiom xiJetQuot_row0_wp2At
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0

/-- Row0 frontier fact at `wp3At`: Toeplitz row0 vanishes. -/
axiom xiJetQuot_row0_wp3At
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
