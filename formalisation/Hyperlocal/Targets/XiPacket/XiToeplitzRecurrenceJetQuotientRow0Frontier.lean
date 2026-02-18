/-
NEW FILE:
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Frontier.lean

Purpose (cycle-breaker):
  Declare the *Route–B row–0 frontier facts* (`xiJetQuot_row0_*`) in a module that
  does NOT import Row0Analytic / Route–C files.

This is exactly the semantic “hinge” you need:
  • Route–C extractor imports THIS file (cycle-safe)
  • Row0Concrete imports THIS file (to re-export or to build downstream wrappers)

Do NOT import Row0Concrete/Row0Analytic here.
-/

import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/-- Route–B frontier: Toeplitz row–0 annihilation for `w0`. -/
axiom xiJetQuot_row0_w0 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s)) (0 : Fin 3) = 0

/-- Route–B frontier: Toeplitz row–0 annihilation for `wc`. -/
axiom xiJetQuot_row0_wc (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s)) (0 : Fin 3) = 0

/-- Route–B frontier: Toeplitz row–0 annihilation for `wp2`. -/
axiom xiJetQuot_row0_wp2 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0

/-- Route–B frontier: Toeplitz row–0 annihilation for `wp3`. -/
axiom xiJetQuot_row0_wp3 (s : OffSeed Xi) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

namespace Row0FrontierExport
export _root_.Hyperlocal.Targets.XiPacket
  (xiJetQuot_row0_w0 xiJetQuot_row0_wc xiJetQuot_row0_wp2 xiJetQuot_row0_wp3)
end Row0FrontierExport

end XiPacket
end Targets
end Hyperlocal
