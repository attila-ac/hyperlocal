/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0FrontierAtOrderSpec.lean

  Axiom-thin interface for Row0 frontier-at-order facts used downstream.

  IMPORTANT:
  * Names are suffixed `_spec` to avoid collisions with the legacy frontier module.
  * This file is intentionally minimal.
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

axiom xiJetQuot_row0_w0At_spec
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0

axiom xiJetQuot_row0_wp2At_spec
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0

axiom xiJetQuot_row0_wp3At_spec
  (m : ℕ) (s : OffSeed Xi) :
  (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
