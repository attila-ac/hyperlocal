/-
  Hyperlocal/Targets/XiPacket/XiRow012StencilGoalsAtOrderDefs.lean

  Defs-only Prop bundle for Path A upstream analytic obligations.

  This isolates the *pure scalar* content needed for the Row012 reverse-stencil:
  the nine convCoeff equalities at n = 3,4,5 for the three canonical AtOrder windows.

  Witness data (∃G, factorisation, IsJet3At) is supplied separately by Route–A
  (`JetQuotOp.xiRouteA_jetPkg`), so it should not be part of the upstream "hard" goal.
-/

import Hyperlocal.Cancellation.Recurrence
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-- Pure scalar stencil goals at order `m` for the three AtOrder windows. -/
structure XiRow012StencilGoalsAtOrder (m : ℕ) (s : OffSeed Xi) : Prop where
  -- w0At
  hw0_3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
  hw0_4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0
  hw0_5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0

  -- wp2At
  hwp2_3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
  hwp2_4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0
  hwp2_5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0

  -- wp3At
  hwp3_3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0
  hwp3_4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0
  hwp3_5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0

end XiPacket
end Targets
end Hyperlocal
