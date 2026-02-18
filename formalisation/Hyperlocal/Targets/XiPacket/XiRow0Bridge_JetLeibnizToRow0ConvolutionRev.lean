/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizToRow0ConvolutionRev.lean

  MOVE-2 frontier collapse (Route–C, Row--0):

      JetLeibnizAt s z w  ⇒  Row0ConvolutionAtRev s z w

  This is the *single* remaining semantic insertion point for Route–C Row--0
  after Move--1 shrank the gate to the single coefficient identity at n=3.

  NOTE:
  The actual proof (Move--3) will later replace this axiom by a theorem.
  For now, this file is cycle-safe and provides exactly ONE axiom.

  Cycle safety:
  * Must not import Row0ConcreteProof / Row0Analytic.
  * Depends only on Leibniz semantics and the Row--0 minimal gate definition.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_LeibnizSemantics
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators

/--
MOVE-2 frontier axiom (to be discharged in MOVE-3):

  JetLeibnizAt s z w ⇒ Row0ConvolutionAtRev s z w.
-/
axiom row0ConvolutionAtRev_of_JetLeibnizAt
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetLeibnizAt s z w → Row0ConvolutionAtRev s z w

namespace JetLeibnizToRow0ConvolutionRevExport
export _root_.Hyperlocal.Targets.XiPacket (row0ConvolutionAtRev_of_JetLeibnizAt)
end JetLeibnizToRow0ConvolutionRevExport

end XiPacket
end Targets
end Hyperlocal
