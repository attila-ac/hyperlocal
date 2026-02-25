/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRow012PropAtOrderProviderTrueAnalytic.lean

  Manuscript-facing TRUE-ANALYTIC gate:

    provide the three Row012 reverse-stencil convolution facts (sigma-free),
    then derive the three ToeplitzRow012Prop facts needed for Rec2.

  This is the exact point where FE/RC/factorisation/analytic identities must land.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticFromToeplitzRow012Prop
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
True-analytic Row012 reverse-stencil convolution gate (sigma-free):

This is *exactly* the analytic content that should come from the manuscript.
-/
class XiRow012ConvolutionAtRevAtOrderTrueAnalytic : Prop where
  hw0At  :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s s.ρ (w0At m s)
  hwp2At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s)
  hwp3At :
    ∀ (m : ℕ) (s : OffSeed Xi),
      Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/--
Now the sigma-free ToeplitzRow012Prop gate follows *purely algebraically*
from `toeplitzRow012Prop_of_row012ConvolutionAtRev`.
-/
instance (priority := 1000)
    [XiRow012ConvolutionAtRevAtOrderTrueAnalytic] :
    XiToeplitzRow012PropAtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_⟩

  · intro m s
    have H : Row012ConvolutionAtRev s s.ρ (w0At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hw0At (m := m) (s := s)
    exact toeplitzRow012Prop_of_row012ConvolutionAtRev (s := s) (z := s.ρ) (w := w0At m s) (H := H)

  · intro m s
    have H : Row012ConvolutionAtRev s ((starRingEnd ℂ) s.ρ) (wp2At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp2At (m := m) (s := s)
    exact toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) (H := H)

  · intro m s
    have H : Row012ConvolutionAtRev s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) :=
      XiRow012ConvolutionAtRevAtOrderTrueAnalytic.hwp3At (m := m) (s := s)
    exact toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) (w := wp3At m s) (H := H)

end XiPacket
end Targets
end Hyperlocal
