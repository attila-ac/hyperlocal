/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetLeibnizToRow0ConvolutionRev.lean

  MOVE–3 (Route–C Row--0), theorem-side retarget.

  Build `Row0ConvolutionAtRev` for the four canonical windows directly from:

    • `JetQuotOpTheorem.xiJetLeibnizAt_w0/wc/wp2/wp3`
        (theorem-side Route–A jet payload)
    • `row0ConvCoeff3_eq_zero_w0/wc/wp2/wp3`
        (Route–B frontier extractor, cycle-safe)

  IMPORTANT:
  * use the theorem namespace explicitly during consumer retarget
  * do NOT import the legacy mixed Route–A JetLeibniz wrapper here
  * do NOT alias theorem-side names back into `JetQuotOp` yet

  2026-03-13 honest post-axiom state:
  * the coeff-3 semantic lane is now theorem-gated
  * therefore this file can no longer remain assumption-free
  * it must expose the honest theorem-side gate

      [XiJetQuotRec2AtOrderTrueAnalytic]
      [TAC.XiJetWindowEqAtOrderQuotProvider]
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizAtFromRouteA_Theorem
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row0Coeff3Semantic
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

/-! ## Canonical `Row0ConvolutionAtRev` instances (theorem-side Route–A retarget) -/

theorem row0ConvolutionAtRev_w0
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row0ConvolutionAtRev s (s.ρ) (w0 s) := by
  have hL : JetLeibnizAt s (s.ρ) (w0 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_w0 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (w0 s)) 3 = 0 :=
    row0ConvCoeff3_eq_zero_w0 (s := s)
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wc
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row0ConvolutionAtRev s (1 - s.ρ) (wc s) := by
  have hL : JetLeibnizAt s (1 - s.ρ) (wc s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wc (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wc s)) 3 = 0 :=
    row0ConvCoeff3_eq_zero_wc (s := s)
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wp2
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row0ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2 s) := by
  have hL : JetLeibnizAt s ((starRingEnd ℂ) s.ρ) (wp2 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wp2 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp2 s)) 3 = 0 :=
    row0ConvCoeff3_eq_zero_wp2 (s := s)
  exact ⟨G, hfac, hjet, h3⟩

theorem row0ConvolutionAtRev_wp3
    (s : OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider] :
    Row0ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) := by
  have hL : JetLeibnizAt s (1 - (starRingEnd ℂ) s.ρ) (wp3 s) :=
    JetQuotOpTheorem.xiJetLeibnizAt_wp3 (s := s)
  rcases hL with ⟨G, hfac, hjet, h0, h1, h2⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev (wp3 s)) 3 = 0 :=
    row0ConvCoeff3_eq_zero_wp3 (s := s)
  exact ⟨G, hfac, hjet, h3⟩

namespace JetLeibnizToRow0ConvolutionRevExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvolutionAtRev_w0
   row0ConvolutionAtRev_wc
   row0ConvolutionAtRev_wp2
   row0ConvolutionAtRev_wp3)
end JetLeibnizToRow0ConvolutionRevExport

end XiPacket
end Targets
end Hyperlocal
