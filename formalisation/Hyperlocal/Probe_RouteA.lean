import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticJetProviderFromJets
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot
import Hyperlocal.Targets.XiPacket.XiRouteA_GDefs
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticAdapterFromUpstream
import Hyperlocal.Targets.XiPacket.XiRow012ConvolutionAtRevAtOrderTrueAnalyticFromUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Hyperlocal.Transport
open Complex

example
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (s.ρ) (w0At m s)]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)] :
    IsJet3AtOrderQuot m s (s.ρ) (w0At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (w0At m s)) :=
    rec2_w0At_trueAnalytic (m := m) (s := s)
  simpa using
    (TAC.isJet3AtOrderQuot_w0At_of_rec2 (m := m) (s := s) (z := s.ρ) hrec)

example
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)] :
    IsJet3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (wp2At m s)) :=
    rec2_wp2At_trueAnalytic (m := m) (s := s)
  simpa using
    (TAC.isJet3AtOrderQuot_wp2At_of_rec2
      (m := m) (s := s) (z := (starRingEnd ℂ) s.ρ) hrec)

example
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider]
    [TAC.JetQuotShiftBridge3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)] :
    IsJet3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  have hrec : JetQuotRec2 s (padSeq3 (wp3At m s)) :=
    rec2_wp3At_trueAnalytic (m := m) (s := s)
  simpa using
    (TAC.isJet3AtOrderQuot_wp3At_of_rec2
      (m := m) (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) hrec)

end XiPacket
end Targets
end Hyperlocal
