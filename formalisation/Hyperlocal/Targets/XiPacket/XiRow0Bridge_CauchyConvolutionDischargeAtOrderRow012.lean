/-
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_CauchyConvolutionDischargeAtOrderRow012.lean

  Purpose:
    Extend the Route–C reverse-convolution semantic gate from the minimal Row–0
    payload (only n=3) to a "row012 stencil" payload (n=3,4,5).

  Key point:
    In `JetConvolutionAtRev`, we assume vanishing for all n ≥ 3,
    hence the Cauchy coefficients at n=3,4,5 are all 0 by projection.

  This file is PURELY ALGEBRAIC / PROJECTION-LEVEL and introduces no new cycles.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchyProductAttempt

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators
open Complex
open Hyperlocal.Cancellation

/--
Row012-strengthened reverse convolution gate:

same witnesses as `JetConvolutionAtRev`, but we retain the three vanishing coefficient
constraints at n = 3,4,5 explicitly.

This is the exact "stencil" payload you will want downstream to manufacture
row-1 / row-2 information via shifts (once the relevant shift lemmas are added),
or to feed a recurrence core extractor.
-/
def Row012ConvolutionAtRev (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) : Prop :=
  ∃ (G : ℂ → ℂ),
    Hyperlocal.Factorization.FactorisedByQuartet Xi s.ρ 1 G ∧
    IsJet3At G z w ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 ∧
    convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0

/-- Projection: full reverse convolution gate implies the row012-stencil gate. -/
theorem row012ConvolutionAtRev_of_JetConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    JetConvolutionAtRev s z w → Row012ConvolutionAtRev s z w := by
  classical
  intro H
  rcases H with ⟨G, hfac, hjet, Htail⟩
  have h3 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 3 = 0 := Htail 3 (by decide)
  have h4 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 4 = 0 := Htail 4 (by decide)
  have h5 : convCoeff (row0CoeffSeqRev s) (winSeqRev w) 5 = 0 := Htail 5 (by decide)
  exact ⟨G, hfac, hjet, h3, h4, h5⟩

/-- Forgetful projection: row012-stencil gate implies the minimal Row–0 gate. -/
theorem row0ConvolutionAtRev_of_row012ConvolutionAtRev
    (s : OffSeed Xi) (z : ℂ) (w : Transport.Window 3) :
    Row012ConvolutionAtRev s z w → Row0ConvolutionAtRev s z w := by
  classical
  intro H
  rcases H with ⟨G, hfac, hjet, h3, h4, h5⟩
  exact ⟨G, hfac, hjet, h3⟩

/-! ### Re-export -/
namespace CauchyConvolutionDischargeAtOrderRow012Export
export _root_.Hyperlocal.Targets.XiPacket
  (Row012ConvolutionAtRev
   row012ConvolutionAtRev_of_JetConvolutionAtRev
   row0ConvolutionAtRev_of_row012ConvolutionAtRev)
end CauchyConvolutionDischargeAtOrderRow012Export

end XiPacket
end Targets
end Hyperlocal
