/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderProviderTrueAnalytic.lean

  TRUE-ANALYTIC landing pad for the Rec2AtOrder provider instance (FULL R0).

  UPDATE (2026-02-27):
  The Row012 reverse-stencil discharge now depends on `[A0Nonzero (s := s)]`
  (because some closed forms divide by `JetQuotOp.aRk1 s 0`).
  We firewall that denominator via `XiRow0Bridge_A0NonzeroBoundary`.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderProvider
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderDefs

-- Real analytic route (extractor-free):
--   Row012 reverse-convolution stencil payload  ⇒  ToeplitzRow012Prop  ⇒  JetQuotRec2 (padSeq3 ...)
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge

-- Boundary for the denominator a0
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_A0NonzeroBoundary

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/-!
## True analytic surface (3 subgoals)
-/

theorem rec2_w0At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [A0Nonzero (s := s)] :
    JetQuotRec2 s (padSeq3 (w0At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hw0 : ToeplitzRow012Prop s (w0At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := s.ρ) (w := w0At m s) Hst.hw0At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := w0At m s) Hw0

theorem rec2_wp2At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [A0Nonzero (s := s)] :
    JetQuotRec2 s (padSeq3 (wp2At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hwp2 : ToeplitzRow012Prop s (wp2At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) Hst.hwp2At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp2At m s) Hwp2

theorem rec2_wp3At_trueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [A0Nonzero (s := s)] :
    JetQuotRec2 s (padSeq3 (wp3At m s)) := by
  classical
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)
  have Hwp3 : ToeplitzRow012Prop s (wp3At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) Hst.hwp3At
  exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp3At m s) Hwp3

/-- Packaged recurrence payload (theorem-level). -/
theorem xiJetQuotRec2AtOrder_fromTrueAnalytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderSigmaProvider] [A0Nonzero (s := s)] :
    XiJetQuotRec2AtOrder m s :=
  ⟨ rec2_w0At_trueAnalytic (m := m) (s := s),
    rec2_wp2At_trueAnalytic (m := m) (s := s),
    rec2_wp3At_trueAnalytic (m := m) (s := s) ⟩

/--
True-analytic Rec2 provider instance (extractor-free).

NOTE:
This instance must match the class field type `∀ m s, ...`, so it cannot demand
`[XiAtOrderSigmaProvider]` or `[A0Nonzero]` at the instance head.
Instead, it *consumes* whatever instances are available at the use site via `letI`.
-/
instance : XiJetQuotRec2AtOrderProvider where
  rec2AtOrder := by
    intro m s
    classical
    letI : XiAtOrderSigmaProvider := by infer_instance
    letI : A0Nonzero (s := s) := by infer_instance
    exact xiJetQuotRec2AtOrder_fromTrueAnalytic (m := m) (s := s)

end XiPacket
end Targets
end Hyperlocal
