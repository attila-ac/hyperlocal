/-
  Formalisation/Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderCoords01FromRec2AtOrderTrueAnalyticStrip.lean

  Strip-specialised theorem wrapper for coords01 from the Rec2-at-order corridor.

  Purpose:
  thread `a0_ne_zero_of_strip` into the existing Rec2 theorem lane without
  touching the global `OffSeed Xi` wrapper.
-/

import Hyperlocal.Transport.OffSeedStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01ProviderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientOperatorNondegeneracyFromStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

theorem xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic_strip
    [XiJetQuotRec2AtOrderProvider]
    (m : ℕ) (s : _root_.Hyperlocal.OffSeedStrip Xi) :
    XiAtOrderCoords01Out m (s : OffSeed Xi) := by
  let s0 : OffSeed Xi := (s : OffSeed Xi)
  letI : A0Nonzero (s := s0) := ⟨by
    simpa [s0] using (a0_ne_zero_of_strip (s := s))
  ⟩
  simpa [s0] using
    (xiAtOrderCoords01Out_fromRec2AtOrderTrueAnalytic (m := m) (s := s0))

end XiPacket
end Targets
end Hyperlocal
