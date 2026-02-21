/-
  Hyperlocal/Targets/XiPacket/XiToeplitzRecurrenceJetQuotientRow012AtOrderFromAnalyticProof.lean

  Task A (2026-02-20): make the analytic row012 landing spot *independent*
  of `Row0SemanticsAtOrder` / `...RecurrenceA`.

  Builds the Type-valued row012 target bundle

    XiJetQuotRow012AtOrder m s

  from the Route–C row012 reverse-convolution stencil payload plus the
  shift-to-Toeplitz bridges.

  IMPORTANT:
    This file must NOT import itself (obviously), and must not introduce
    the extractor stack.
-/

import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderRow012Target

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromAnalytic
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionToToeplitzRow012Prop

import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Cycle-safe analytic landing construction (Type-valued row012 target bundle).

This is independent of the old RecurrenceA/Row0Semantics path.
-/
noncomputable def xiJetQuotRow012AtOrder_fromAnalyticProof
    (m : ℕ) (s : OffSeed Xi) : XiJetQuotRow012AtOrder m s := by
  classical

  -- (A) obtain the row012-stencil payload for the three AtOrder windows
  have Hst : XiRow012ConvolutionAtRevAtOrderOut m s :=
    xiRow012ConvolutionAtRevAtOrderOut_fromAnalytic (m := m) (s := s)

  -- derive Prop-level row012 Toeplitz payloads for each AtOrder window
  have Hw0  : ToeplitzRow012Prop s (w0At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev (s := s) (z := s.ρ) (w := w0At m s) Hst.hw0At
  have Hwp2 : ToeplitzRow012Prop s (wp2At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (starRingEnd ℂ) s.ρ) (w := wp2At m s) Hst.hwp2At
  have Hwp3 : ToeplitzRow012Prop s (wp3At m s) :=
    toeplitzRow012Prop_of_row012ConvolutionAtRev
      (s := s) (z := (1 - (starRingEnd ℂ) s.ρ)) (w := wp3At m s) Hst.hwp3At

  -- package the row-0 witness and the row-1/row-2 equalities
  have hrow0 : XiJetQuotRow0WitnessCAtOrder m s := by
    exact ⟨Hw0.h0, Hwp2.h0, Hwp3.h0⟩

  exact
    { h0 := hrow0
      h1_w0At := Hw0.h1
      h2_w0At := Hw0.h2
      h1_wp2At := Hwp2.h1
      h2_wp2At := Hwp2.h2
      h1_wp3At := Hwp3.h1
      h2_wp3At := Hwp3.h2 }

end XiPacket
end Targets
end Hyperlocal
