/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalytic.lean

  Theorem-side extra-lin bridge from the true-analytic Rec2 corridor.

  2026-03-12 surgical retarget:
  * remove the explicit `[A0Nonzero (s := s)]` seam from the global OffSeed wrapper
  * do NOT import `XiRow0Bridge_A0NonzeroBoundary`
  * avoid the upstream provider-core cone
  * route through:
      true-analytic -> critical strip -> strip extra-lin theorem
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Transport

theorem xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (m : ℕ) (s : OffSeed Xi) :
    XiRow012ExtraLinAtOrderOut m s := by
  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : (ss : OffSeed Xi) = s := by
    rfl
  simpa [hs] using
    (xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip
      (m := m) (s := ss))

end XiPacket
end Targets
end Hyperlocal
