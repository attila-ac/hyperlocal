/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrder.lean

  AtOrder Route–B semantics (public surface).

  Definitions are in:
    XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs.lean

  Provider refactor (2026-02-22):
  `xiJetQuotOpZeroAtOrder_fromRecurrenceA` consumes the recurrence payload via
  a typeclass `[XiJetQuotRec2AtOrderProvider]`.

  DISCHARGE STEP (2026-02-22):
  This public surface now installs the *theorem-level* provider instance from the
  analytic extractor glue:

    XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderFromAnalyticExtractor.lean

  so downstream consumers do not see the axiom provider by default.

  NOTE:
  This file is intentionally NOT “true analytic”: it is a public surface file that
  may import extractor-facing glue. Analytic-only upstream modules must not import it.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs

-- Install theorem-level provider instance (non-cycle-safe glue, extractor-facing).
--
-- 2026-02-22 (Task A3): switch the default provider to the (now theorem-level)
-- true-analytic provider instance.
--
-- This keeps the public Route–B semantics chain extractor-free by default.
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic

-- Theorem-level construction of OpZero from the provided recurrence payload.
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Route–B recurrence-natural semantic output.

We explicitly install the provider instance with `letI` to avoid
elaboration-order / typeclass-synthesis brittleness.
-/
theorem xiJetQuotOpZeroAtOrder (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  letI : XiJetQuotRec2AtOrderProvider := by infer_instance
  exact xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s)

/-- Derived row-0 witness bundle (projection of the full-window contract). -/
noncomputable def xiJetQuotRow0WitnessCAtOrder (m : ℕ) (s : OffSeed Xi) :
    XiJetQuotRow0WitnessCAtOrder m s := by
  classical
  letI : XiJetQuotRec2AtOrderProvider := by infer_instance
  exact xiJetQuotRow0WitnessCAtOrder_of_opZero (m := m) (s := s)
    (xiJetQuotOpZeroAtOrder_fromRecurrenceA (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
