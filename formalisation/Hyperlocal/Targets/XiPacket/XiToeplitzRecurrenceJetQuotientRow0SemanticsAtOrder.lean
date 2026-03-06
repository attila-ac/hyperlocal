/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  AtOrder Route–B semantics (public surface).

  Definitions are in:
    XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  Provider refactor (2026-02-22):
  `xiJetQuotOpZeroAtOrder_fromRecurrenceA` consumes the recurrence payload via
  a typeclass `[XiJetQuotRec2AtOrderProvider]`.

  LOCAL-CLEAN-PROVIDER TEST STEP:
  The historical public wrapper now calls the already-clean theorem route
    `xiJetQuotOpZeroAtOrder_fromRecurrenceA`
  but with a locally installed clean recurrence provider backed by
    `xiJetQuotRec2AtOrder_fromRow012Upstream`.

  IMPORTANT:
  * do not touch shared historical provider files
  * install only local theorem-backed instances here
  * this tests whether the dirty cone is entering through the default global
    `XiJetQuotRec2AtOrderProvider` instance selection
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromRow012Upstream
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs

/-
  DISCHARGE STEP (2026-02-25):
  This public surface installs the recurrence payload via the Prop-interface gate
  `XiJetQuotRec2AtOrderTrueAnalytic` (adapter-from-provider).
  This keeps the default Route–B semantics extractor-free by imports.
-/
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticAdapterFromProvider

-- theorem-level construction helpers
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

-- theorem-level clean coords source
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01FromSigmaAndRow012TrueAnalytic

-- canonical producer for `[XiRow012ConvolutionAtRevAtOrderTrueAnalytic]`
import Hyperlocal.Targets.XiPacket.XiToeplitzRow012PropAtOrderProviderTrueAnalytic_Row012ConvolutionInstanceFromUpstream

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators
open Hyperlocal.Transport

/--
Local theorem-level coords provider from clean sigma + Row012 true-analytic.
This is installer-free and used only to freeze the intended route into the
historical public theorem surface.
-/
private def xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiAtOrderCoords01Provider where
  coords01 := by
    intro m s
    classical
    exact xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic (m := m) (s := s)

/--
Local clean recurrence provider, backed by the Row012-upstream theorem route and
the local clean coords provider above.
-/
private def xiJetQuotRec2AtOrderProvider_fromRow012Upstream
    [XiAtOrderSigmaProvider]
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic]
    [XiSigma3Nonzero] :
    XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    letI : XiAtOrderCoords01Provider :=
      xiAtOrderCoords01Provider_fromSigmaAndRow012TrueAnalytic
    exact xiJetQuotRec2AtOrder_fromRow012Upstream (m := m) (s := s)

/--
Explicit row-0 extraction from a supplied recurrence payload.
This duplicates only the small recurrence-to-row lemmas so the public wrapper
can avoid the provider graph completely.
-/
private lemma row0_eq_zero_of_rec2_explicit
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (0 : Fin 3) = 0 := by
  have h0' :
      (JetQuotOp.aRk1 s 0) * w 0
        + (JetQuotOp.aRk1 s 1) * w 1
        + (JetQuotOp.aRk1 s 2) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 0)
  simpa [toeplitzL_two_apply_fin0, add_assoc, add_left_comm, add_comm] using h0'

private lemma row1_eq_zero_of_rec2_explicit
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (1 : Fin 3) = 0 := by
  have h1' :
      (JetQuotOp.aRk1 s 0) * w 1
        + (JetQuotOp.aRk1 s 1) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 1)
  simpa [toeplitzL_two_apply_fin1, add_assoc, add_left_comm, add_comm] using h1'

private lemma row2_eq_zero_of_rec2_explicit
    (s : OffSeed Xi) (w : Window 3)
    (hrec : JetQuotRec2 s (padSeq3 w)) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) w) (2 : Fin 3) = 0 := by
  have h2' : (JetQuotOp.aRk1 s 0) * w 2 = 0 := by
    simpa [JetQuotRec2, padSeq3, Nat.add_assoc] using (hrec 2)
  simpa [toeplitzL_two_apply_fin2] using h2'

/--
Direct explicit construction of OpZero from a supplied recurrence payload.
This avoids any use of `[XiJetQuotRec2AtOrderProvider]` at the public wrapper site.
-/
private theorem xiJetQuotOpZeroAtOrder_of_explicitRec2
    (m : ℕ) (s : OffSeed Xi)
    (Hrec : XiJetQuotRec2AtOrder m s) :
    XiJetQuotOpZeroAtOrder m s := by
  have h0_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2_explicit (s := s) (w := w0At m s) Hrec.h_w0At
  have h0_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2_explicit (s := s) (w := wp2At m s) Hrec.h_wp2At
  have h0_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
    row0_eq_zero_of_rec2_explicit (s := s) (w := wp3At m s) Hrec.h_wp3At

  have h0 : XiJetQuotRow0WitnessCAtOrder m s := ⟨h0_w0At, h0_wp2At, h0_wp3At⟩

  have h1_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2_explicit (s := s) (w := w0At m s) Hrec.h_w0At
  have h2_w0At  : (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2_explicit (s := s) (w := w0At m s) Hrec.h_w0At

  have h1_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2_explicit (s := s) (w := wp2At m s) Hrec.h_wp2At
  have h2_wp2At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2_explicit (s := s) (w := wp2At m s) Hrec.h_wp2At

  have h1_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (1 : Fin 3) = 0 :=
    row1_eq_zero_of_rec2_explicit (s := s) (w := wp3At m s) Hrec.h_wp3At
  have h2_wp3At : (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (2 : Fin 3) = 0 :=
    row2_eq_zero_of_rec2_explicit (s := s) (w := wp3At m s) Hrec.h_wp3At

  exact xiJetQuotOpZeroAtOrder_of_row012
    (m := m) (s := s)
    (h0 := h0)
    (h1_w0At := h1_w0At)   (h2_w0At := h2_w0At)
    (h1_wp2At := h1_wp2At) (h2_wp2At := h2_wp2At)
    (h1_wp3At := h1_wp3At) (h2_wp3At := h2_wp3At)

/--
Route–B recurrence-natural semantic output.

Public wrapper: call the clean theorem-level route from
`...FromRecurrenceA`, but with a local clean `XiJetQuotRec2AtOrderProvider`.
-/
theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  letI : XiAtOrderSigmaProvider := by infer_instance
  letI : XiRow012ConvolutionAtRevAtOrderTrueAnalytic := by infer_instance
  letI : XiSigma3Nonzero := by infer_instance
  letI : XiJetQuotRec2AtOrderProvider :=
    xiJetQuotRec2AtOrderProvider_fromRow012Upstream
  exact xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s)

/-- Derived row-0 witness bundle (projection of the full-window contract). -/
noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
