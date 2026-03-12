/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge.lean

  Parallel theorem-side discharge of the Row012 AtOrder reverse-stencil payload
  through the ROOT-FREE Rec2-at-order coords/extra-lin corridor.

  IMPORTANT:
  * theorem-level only
  * does NOT import the analytic extractor coords corridor
  * keeps the historical analytic discharge file unchanged
  * adds the explicit Rec2 provider gate where needed

  2026-03-11:
  Retargeted from the legacy ambient Route-A Leibniz wrapper to the
  theorem-side wrapper with explicit gate
    [TAC.XiJetWindowEqAtOrderQuotProvider].

  2026-03-12 surgical retarget:
  * remove the explicit `[A0Nonzero (s := s)]` dependency from this Rec2 discharge lane
  * derive the strip object from the true-analytic critical-strip bridge
  * obtain the extra-linear payload through the strip-specialised theorem lane
    instead of consuming the legacy ambient `A0Nonzero` seam directly
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalyticStrip
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce
import Hyperlocal.Targets.XiPacket.XiTrueAnalyticCriticalStripBridge
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem row012ConvolutionAtRev_w0At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s s.ρ (w0At m s) := by
  classical
  letI : XiAtOrderSigmaProvider := inferInstance
  letI : XiJetQuotRec2AtOrderProvider := inferInstance

  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : (ss : OffSeed Xi) = s := by
    rfl

  have HLall : XiRow012ExtraLinAtOrderOut m (ss : OffSeed Xi) :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip (m := m) (s := ss)
  have HL : Row012ExtraLin s (w0At m s) := by
    simpa [hs] using HLall.hw0At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_w0At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
    have hsigma : row0Sigma s (w0At m s) = 0 := H.hw0AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hsigma

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := w0At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := w0At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp2At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  letI : XiAtOrderSigmaProvider := inferInstance
  letI : XiJetQuotRec2AtOrderProvider := inferInstance

  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : (ss : OffSeed Xi) = s := by
    rfl

  have HLall : XiRow012ExtraLinAtOrderOut m (ss : OffSeed Xi) :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip (m := m) (s := ss)
  have HL : Row012ExtraLin s (wp2At m s) := by
    simpa [hs] using HLall.hwp2At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp2At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
    have hsigma : row0Sigma s (wp2At m s) = 0 := H.hwp2AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hsigma

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp2At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp2At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp3At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  letI : XiAtOrderSigmaProvider := inferInstance
  letI : XiJetQuotRec2AtOrderProvider := inferInstance

  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  rcases hstrip : offSeed_in_critical_strip_of_trueanalytic (m := m) (s := s) with
    ⟨hRe_pos, hRe_lt_one⟩
  let ss : _root_.Hyperlocal.OffSeedStrip Xi :=
    Hyperlocal.mkOffSeedStrip (s := s) (hRe_pos := hRe_pos) (hRe_lt_one := hRe_lt_one)
  have hs : (ss : OffSeed Xi) = s := by
    rfl

  have HLall : XiRow012ExtraLinAtOrderOut m (ss : OffSeed Xi) :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic_strip (m := m) (s := ss)
  have HL : Row012ExtraLin s (wp3At m s) := by
    simpa [hs] using HLall.hwp3At

  rcases JetQuotOpTheorem.xiRouteA_jetPkg_wp3At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
    have hsigma : row0Sigma s (wp3At m s) = 0 := H.hwp3AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hsigma

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp3At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp3At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_discharge
    (m : ℕ) (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row012ConvolutionAtRev_w0At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  · exact row012ConvolutionAtRev_wp2At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  · exact row012ConvolutionAtRev_wp3At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
