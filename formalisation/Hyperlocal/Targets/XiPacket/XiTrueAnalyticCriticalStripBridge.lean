import Hyperlocal.Transport.OffSeedStripBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderRec2TrueAnalyticRoot

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

axiom offSeed_in_critical_strip_of_trueanalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    0 < s.ρ.re ∧ s.ρ.re < 1

noncomputable def offSeedStrip_of_trueanalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    _root_.Hyperlocal.OffSeedStrip Xi := by
  rcases offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with ⟨hRe_pos, hRe_lt_one⟩
  exact mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)

end XiPacket
end Targets
end Hyperlocal
