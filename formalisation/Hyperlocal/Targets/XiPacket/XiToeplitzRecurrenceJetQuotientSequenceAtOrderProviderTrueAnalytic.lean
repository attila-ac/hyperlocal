/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean

  TRUE-ANALYTIC landing pad for the Rec2AtOrder provider instance (FULL R0).

  Goal (final):
    instance : XiJetQuotRec2AtOrderProvider

  DAG contract:
  * Only "true analytic" imports (FE/RC/factorisation/jet identities / manuscript).
  * MUST NOT import extractor-facing modules.
  * MUST NOT import Row012 analytic endpoint modules, i.e.
      XiToeplitzRecurrenceJetQuotientRow012AtOrderAnalyticAxiom.lean
    or anything that depends on it.

  Status (2026-02-22):
  * The three Rec2 facts are theorem-level (no local axioms here).
  * This file remains extractor-free; the only remaining cliffs are upstream
    provider/axiom boundaries (sigma / Route-A jet package / nondegeneracy), but
    those are now firewall-separated.

  IMPORTANT:
  `XiJetQuotRec2AtOrderProvider.rec2AtOrder` is a field of type
    ∀ m s, XiJetQuotRec2AtOrder m s
  so the provider instance itself cannot require extra typeclass arguments.
  Any needed instances must be consumed internally (via `letI`) or appear only
  in theorems, not in the class field type.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

-- Real analytic route (extractor-free):
--   Row012 reverse-convolution stencil payload  ⇒  ToeplitzRow012Prop  ⇒  JetQuotRec2 (padSeq3 ...)
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## True analytic surface (3 subgoals)

These are exactly the three recurrence facts to prove (theorem-level, extractor-free):

  JetQuotRec2 s (padSeq3 (w0At  m s))
  JetQuotRec2 s (padSeq3 (wp2At m s))
  JetQuotRec2 s (padSeq3 (wp3At m s))

NOTE:
`xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic` is parametric in `[XiAtOrderSigmaProvider]`,
so each theorem below is also parametric in that instance.
-/

theorem rec2_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hw0 : ToeplitzRow012Prop s (w0At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) Hst.hw0At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := w0At m s) Hw0

theorem rec2_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hwp2 : ToeplitzRow012Prop s (wp2At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) Hst.hwp2At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp2At m s) Hwp2

theorem rec2_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hwp3 : ToeplitzRow012Prop s (wp3At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) Hst.hwp3At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp3At m s) Hwp3

/-- Packaged recurrence payload (theorem-level, extractor-free once sigma is provided). -/
theorem xiJetQuotRec2AtOrder_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] :
    XiJetQuotRec2AtOrder m s :=
  ⟨ rec2_w0At_trueAnalytic (m := m) (s := s),
    rec2_wp2At_trueAnalytic (m := m) (s := s),
    rec2_wp3At_trueAnalytic (m := m) (s := s) ⟩

/--
True-analytic Rec2 provider instance (extractor-free).

NOTE:
This instance must match the class field type `∀ m s, ...`, so it cannot demand
`[XiAtOrderSigmaProvider]` at the instance head. Instead, it *consumes* whatever
sigma provider is in scope at the use site via `letI` + `infer_instance`.

This keeps the core DAG cycle-safe: upstream files remain parametric; leafy public
surfaces install the sigma provider instance when desired.
-/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    -- Require sigma at use sites, not at import time.
    letI : XiAtOrderSigmaProvider := by infer_instance
    exact xiJetQuotRec2AtOrder_fromTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
