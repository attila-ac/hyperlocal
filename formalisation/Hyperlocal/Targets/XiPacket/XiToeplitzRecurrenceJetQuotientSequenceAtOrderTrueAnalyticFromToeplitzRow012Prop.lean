/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticFromToeplitzRow012Prop.lean

  Sigma-free TRUE-ANALYTIC gate for the Rec2 interface.

  Instead of proving Rec2 via:
      Row012ConvolutionAtRevAtOrderOut (needs sigma)
        ⇒ ToeplitzRow012Prop
        ⇒ JetQuotRec2,
  we make the “manuscript-facing” analytic burden explicit as a tiny Prop-gate:

      [XiToeplitzRow012PropAtOrderTrueAnalytic]
        ⇒ [XiJetQuotRec2AtOrderTrueAnalytic]

  This is the right direction for Lean 28:
  Rec2 becomes the *source* of sigma (frontier-free), not a consumer of sigma.

  Later:
  - Discharge XiToeplitzRow012PropAtOrderTrueAnalytic directly from FE/RC/factorisation,
    without importing any sigma/frontier/extractor modules.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceAtOrderTrueAnalyticInterface
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientSequenceToRow012Bridge
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Sigma-free analytic gate (manuscript target):

Provide `ToeplitzRow012Prop` for the three canonical AtOrder windows.

This is strictly *stronger* than the convCoeff-3-only gate you deleted, but it is
exactly what your current Rec2 derivation uses anyway — except today you obtain it
via `Row012ConvolutionAtRevAtOrderOut` + sigma.

Endgame: prove these directly from analytic identities (FE/RC/etc.).
-/
class XiToeplitzRow012PropAtOrderTrueAnalytic : Prop where
  toeplitz_w0At  : ∀ (m : ℕ) (s : OffSeed Xi), ToeplitzRow012Prop s (w0At m s)
  toeplitz_wp2At : ∀ (m : ℕ) (s : OffSeed Xi), ToeplitzRow012Prop s (wp2At m s)
  toeplitz_wp3At : ∀ (m : ℕ) (s : OffSeed Xi), ToeplitzRow012Prop s (wp3At m s)

/--
From the sigma-free ToeplitzRow012Prop gate, Rec2 follows immediately by the existing
algebraic bridge `jetQuotRec2_padSeq3_of_toeplitzRow012Prop`.
-/
instance (priority := 1000)
    [XiToeplitzRow012PropAtOrderTrueAnalytic] :
    XiJetQuotRec2AtOrderTrueAnalytic := by
  refine ⟨?_, ?_, ?_⟩
  · intro m s
    have H : ToeplitzRow012Prop s (w0At m s) :=
      XiToeplitzRow012PropAtOrderTrueAnalytic.toeplitz_w0At (m := m) (s := s)
    exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := w0At m s) H
  · intro m s
    have H : ToeplitzRow012Prop s (wp2At m s) :=
      XiToeplitzRow012PropAtOrderTrueAnalytic.toeplitz_wp2At (m := m) (s := s)
    exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp2At m s) H
  · intro m s
    have H : ToeplitzRow012Prop s (wp3At m s) :=
      XiToeplitzRow012PropAtOrderTrueAnalytic.toeplitz_wp3At (m := m) (s := s)
    exact jetQuotRec2_padSeq3_of_toeplitzRow012Prop (s := s) (w := wp3At m s) H

end XiPacket
end Targets
end Hyperlocal
