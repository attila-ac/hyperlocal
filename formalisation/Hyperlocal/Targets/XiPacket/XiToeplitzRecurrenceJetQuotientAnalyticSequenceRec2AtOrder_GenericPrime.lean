import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface_GenericPrime

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport

def JPAt (m : ℕ) (s : OffSeed Xi) (p : ℕ) : ℕ → ℂ :=
  padSeq3 (wpAt m s p)

@[simp] lemma JPAt_def (m : ℕ) (s : OffSeed Xi) (p : ℕ) :
    JPAt m s p = padSeq3 (wpAt m s p) := rfl

theorem jetQuotRec2_JPAt_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalyticPrime] :
    JetQuotRec2 s (JPAt m s p) := by
  simpa [JPAt] using
    XiJetQuotRec2AtOrderTrueAnalyticPrime.rec2_wpAt (m := m) (s := s) (p := p)

end XiPacket
end Targets
end Hyperlocal
