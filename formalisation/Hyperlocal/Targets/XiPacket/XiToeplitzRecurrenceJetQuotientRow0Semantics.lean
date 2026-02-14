/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0Semantics.lean

  Pure *statement* layer: the row-0 annihilation witness type for Route B.

  The actual ξ-semantic content lives in the `...Row0Bridge` file, which provides
  `xiJetQuotRow0WitnessC` as a theorem.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorDefs
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.Transport.TACToeplitz

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Hyperlocal.Transport

/-- C-only row-0 annihilation witness for the jet-quotient Toeplitz operator on the
four canonical ξ windows `w0/wc/wp2/wp3`. -/
structure XiJetQuotRow0WitnessC (s : Hyperlocal.OffSeed Xi) : Type where
  hop_w0  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0 s))  (0 : Fin 3) = 0
  hop_wc  : (toeplitzL 2 (JetQuotOp.aRk1 s) (wc s))  (0 : Fin 3) = 0
  hop_wp2 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2 s)) (0 : Fin 3) = 0
  hop_wp3 : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3 s)) (0 : Fin 3) = 0

-- NOTE: the ξ-semantic content (recurrence extraction) is moved to the
-- `...Row0Bridge` layer, so downstream plumbing can import a theorem rather
-- than a raw axiom.

end XiPacket
end Targets
end Hyperlocal
