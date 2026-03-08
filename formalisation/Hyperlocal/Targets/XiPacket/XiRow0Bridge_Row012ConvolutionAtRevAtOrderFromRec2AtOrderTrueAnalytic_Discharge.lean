/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromRec2AtOrderTrueAnalytic_Discharge.lean

  Parallel theorem-side discharge of the Row012 AtOrder reverse-stencil payload
  through the ROOT-FREE Rec2-at-order coords/extra-lin corridor.

  IMPORTANT:
  * theorem-level only
  * does NOT import the analytic extractor coords corridor
  * keeps the historical analytic discharge file unchanged
  * adds the explicit Rec2 provider gate where needed
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0ConcreteExtractAtOrderHeart
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinAtOrderFromRec2AtOrderTrueAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic_Reduce
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

theorem row012ConvolutionAtRev_w0At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiJetQuotRec2AtOrderProvider] [A0Nonzero (s := s)] :
    Row012ConvolutionAtRev s (s.ρ) (w0At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  have HL : Row012ExtraLin s (w0At m s) := HLall.hw0At

  rcases JetQuotOp.xiRouteA_jetPkg_w0At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 3 = 0 := by
    have hs : row0Sigma s (w0At m s) = 0 := H.hw0AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := w0At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := w0At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := w0At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp2At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiJetQuotRec2AtOrderProvider] [A0Nonzero (s := s)] :
    Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  have HL : Row012ExtraLin s (wp2At m s) := HLall.hwp2At

  rcases JetQuotOp.xiRouteA_jetPkg_wp2At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 3 = 0 := by
    have hs : row0Sigma s (wp2At m s) = 0 := H.hwp2AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp2At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp2At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp2At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem row012ConvolutionAtRev_wp3At_fromRec2AtOrderTrueAnalytic
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiJetQuotRec2AtOrderProvider] [A0Nonzero (s := s)] :
    Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  have H : XiJetQuotRow0AtOrderHeartOut m s :=
    xiJetQuotRow0AtOrderHeartOut (m := m) (s := s)

  have HLall : XiRow012ExtraLinAtOrderOut m s :=
    xiRow012ExtraLinAtOrderOut_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  have HL : Row012ExtraLin s (wp3At m s) := HLall.hwp3At

  rcases JetQuotOp.xiRouteA_jetPkg_wp3At (m := m) (s := s) with
    ⟨G, hfac, hjet, _, _, _, _⟩

  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 3 = 0 := by
    have hs : row0Sigma s (wp3At m s) = 0 := H.hwp3AtSigma
    simpa [row0Sigma_eq_convCoeff_rev (s := s) (w := wp3At m s)] using hs

  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 4 = 0 := by
    rw [convCoeff_rev_eq_n4 (s := s) (w := wp3At m s)]
    simpa using HL.h4

  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3At m s)) 5 = 0 := by
    rw [convCoeff_rev_eq_n5 (s := s) (w := wp3At m s)]
    simpa using HL.h5

  exact ⟨G, hfac, hjet, h3, h4, h5⟩

theorem xiRow012ConvolutionAtRevAtOrderOut_fromRec2AtOrderTrueAnalytic_discharge
    (m : ℕ) (s : OffSeed Xi)
    [XiAtOrderSigmaProvider] [XiJetQuotRec2AtOrderProvider] [A0Nonzero (s := s)] :
    XiRow012ConvolutionAtRevAtOrderOut m s := by
  refine ⟨?_, ?_, ?_⟩
  · exact row012ConvolutionAtRev_w0At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  · exact row012ConvolutionAtRev_wp2At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)
  · exact row012ConvolutionAtRev_wp3At_fromRec2AtOrderTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
