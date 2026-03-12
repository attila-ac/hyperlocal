import Hyperlocal.Targets.XiPacket.XiSigma3Nonzero
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiSigma3NonzeroFromStrip

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

theorem sigma3_ne_zero_of_trueanalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    (JetQuotOp.σ3 s : ℂ) ≠ 0 := by
  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : ss.toOffSeed = s := by
    rfl
  simpa [ss, hs] using sigma3_ne_zero_of_strip (s := ss)

instance (priority := 950)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiSigma3Nonzero where
  sigma3_ne_zero := by
    intro s
    exact sigma3_ne_zero_of_trueanalytic (m := 0) (s := s)

end XiPacket
end Targets
end Hyperlocal
