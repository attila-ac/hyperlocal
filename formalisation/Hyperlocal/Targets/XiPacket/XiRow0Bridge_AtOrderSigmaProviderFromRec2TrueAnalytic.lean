/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic.lean

  Extractor-free glue (frontier-free): derive the sigma provider instance at order `m`
  from the Prop-class recurrence gate:

    [XiJetQuotRec2AtOrderTrueAnalytic].

  Strategy:
  * Use the standard Rec2→OpZero construction
      `xiJetQuotOpZeroAtOrder_fromRecurrenceA`
    (which consumes `[XiJetQuotRec2AtOrderProvider]`).
  * Project the row-0 ToeplitzL equalities at index `(0 : Fin 3)` for `w0At/wp2At/wp3At`
    via `xiJetQuotRow0WitnessCAtOrder_of_opZero`.
  * Rewrite row-0 ToeplitzL into `row0Sigma` via the pure-algebra lemma
      `toeplitzL_row0_eq_row0Sigma`.

  This removes the dependency on the Route–B Row0 frontier-at-order projections.
  No axioms introduced.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-- Sigma bundle at order derived from the Rec2 true-analytic interface. -/
theorem xiAtOrderSigmaOut_fromRec2TrueAnalytic
    [XiJetQuotRec2AtOrderTrueAnalytic] (m : ℕ) (s : OffSeed Xi) : XiAtOrderSigmaOut m s := by
  classical
  -- Consume the interface through the standard bundled provider.
  letI : XiJetQuotRec2AtOrderProvider := by infer_instance

  -- Build the full-window OpZero payload from Rec2.
  have Hop : XiJetQuotOpZeroAtOrder m s :=
    xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s)

  -- Project to row-0 equalities at index 0.
  have Hw : XiJetQuotRow0WitnessCAtOrder m s :=
    xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s) Hop

  refine ⟨?_, ?_, ?_⟩
  · -- w0At
    have ht :
        (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) (0 : Fin 3) = 0 :=
      Hw.hop_w0At
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := w0At m s)
    simpa [hrew] using ht
  · -- wp2At
    have ht :
        (toeplitzL 2 (JetQuotOp.aRk1 s) (wp2At m s)) (0 : Fin 3) = 0 :=
      Hw.hop_wp2At
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp2At m s)
    simpa [hrew] using ht
  · -- wp3At
    have ht :
        (toeplitzL 2 (JetQuotOp.aRk1 s) (wp3At m s)) (0 : Fin 3) = 0 :=
      Hw.hop_wp3At
    have hrew := toeplitzL_row0_eq_row0Sigma (s := s) (w := wp3At m s)
    simpa [hrew] using ht

/-- Provider instance derived from `[XiJetQuotRec2AtOrderTrueAnalytic]` (frontier-free). -/
instance (priority := 1000)
    [XiJetQuotRec2AtOrderTrueAnalytic] : XiAtOrderSigmaProvider where
  sigma := xiAtOrderSigmaOut_fromRec2TrueAnalytic

end XiPacket
end Targets
end Hyperlocal
