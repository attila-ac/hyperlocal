/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic_JetConvolutionTail345Interface.lean

  Push C interface (cycle-safe):

  The "real" tail gate used by JetConvolutionDischarge:
    XiJetConvolutionTail345AtOrderTrueAnalytic

  This file exists ONLY to break the import cycle.

  FIX (2026-02-28):
  `row0CoeffSeqRev` and `winSeqRev` live in `XiRow0Bridge_CauchyProductAttempt`,
  so we import that here (NOT JetConvolutionDischarge).
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

-- for `convCoeff`
import Hyperlocal.Cancellation.Recurrence

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/--
REAL tail gate (ONLY the real obligations):

Provide the reverse-Cauchy coefficient vanishings at n = 3,4,5
for the three canonical AtOrder windows.
-/
class XiJetConvolutionTail345AtOrderTrueAnalytic : Prop where
  tail3_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0
  tail4_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0
  tail5_w0At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0

  tail3_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0
  tail4_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0
  tail5_wp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0

  tail3_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0
  tail4_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0
  tail5_wp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0

end XiPacket
end Targets
end Hyperlocal
