/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target.lean

  Route–A landing pad: explicit “row012” target bundle.

  This is the exact shape the eventual recurrence extractor should output:
  row0 witness + row1/row2 scalar equalities for w0At/wp2At/wp3At.

  From this bundle, full-window annihilation follows via
  `xiJetQuotOpZeroAtOrder_of_row012` (already in the landing pad).
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- “Row012” scalar payload sufficient to build full Window-3 annihilation. -/
structure XiJetQuotRow012AtOrder (m : ℕ) (s : OffSeed Xi) : Type where
  h0 : XiJetQuotRow0WitnessCAtOrder m s

  h1_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (1 : Fin 3) = 0
  h2_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s))  (2 : Fin 3) = 0

  h1_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (1 : Fin 3) = 0
  h2_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (2 : Fin 3) = 0

  h1_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (1 : Fin 3) = 0
  h2_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (2 : Fin 3) = 0

end XiPacket
end Targets
end Hyperlocal
