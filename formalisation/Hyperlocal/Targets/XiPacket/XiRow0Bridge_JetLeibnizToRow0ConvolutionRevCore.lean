import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Complex
open scoped BigOperators
open Hyperlocal.Cancellation

/-
  Parametric core:
  build `Row0ConvolutionAtRev` from theorem-side JetLeibniz plus an abstract
  coeff-3 vanishing input. This is the cycle-safe insertion point for the final
  independent `wc` producer.
-/

theorem row0ConvolutionAtRev_w0_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0) :
    Row0ConvolutionAtRev s (s.ρ) (w0 s) := by
  have hL : JetLeibnizAt s (s.ρ) (w0 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_w0 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wc_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0) :
    Row0ConvolutionAtRev s (1 - s.ρ) (wc s) := by
  have hL : JetLeibnizAt s (1 - s.ρ) (wc s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wc (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wp2_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0) :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  have hL : JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wp2 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wp3_of_coeff3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0) :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  have hL : JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wp3 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  exact ⟨G, hfac, hjet, h3⟩

end XiPacket
end Targets
end Hyperlocal
