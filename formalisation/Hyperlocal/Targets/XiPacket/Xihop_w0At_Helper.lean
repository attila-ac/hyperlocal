/-
  Hyperlocal/Targets/XiPacket/Xihop_w0At_Helper.lean

  Helper: derive `hop_w0At` (and wp2/wp3) for `XiJetQuotOpZeroAtOrder`
  from the Row012 reverse-convolution AtOrder payload bundle.

  IMPORTANT:
  In this repo the AtOrder Row012 payload is:
      XiRow012ConvolutionAtRevAtOrderOut m s
  (NOT a class named `XiRow012ConvolutionAtRevAtOrder`).
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevToRow012PropAtOrder
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderDefs
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceJetQuotientRow0SemanticsAtOrderFromRecurrenceA

-- optional: if you want a theorem-level source of the Out-bundle from true-analytic
-- (Rec2-gated) landing pads, uncomment:
-- import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ConvolutionAtRevAtOrderFromTrueAnalytic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

/--
Core constructor:
Row012 reverse-convolution bundle (AtOrder) ⇒ full-window Toeplitz annihilation bundle (AtOrder).
-/
theorem xiJetQuotOpZeroAtOrder_of_row012ConvolutionAtRevAtOrderOut
    (m : ℕ) (s : OffSeed Xi)
    (H : XiRow012ConvolutionAtRevAtOrderOut m s) :
    XiJetQuotOpZeroAtOrder m s := by
  classical

  -- First upgrade the Row012 reverse-convolution payload into row012 Toeplitz equalities.
  have Hprop : XiJetQuotRow012PropAtOrder m s :=
    xiJetQuotRow012PropAtOrder_of_row012ConvolutionAtRevAtOrder (m := m) (s := s) H

  -- Unpack the three row012 payloads.
  have hw0  : ToeplitzRow012Prop s (w0At m s)  := Hprop.1
  have hwp2 : ToeplitzRow012Prop s (wp2At m s) := Hprop.2.1
  have hwp3 : ToeplitzRow012Prop s (wp3At m s) := Hprop.2.2

  -- Assemble full-window equalities by ext on `Fin 3` using the row0/1/2 equalities.
  refine ⟨?_, ?_, ?_⟩
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := w0At m s)
      (h0 := hw0.h0) (h1 := hw0.h1) (h2 := hw0.h2)
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := wp2At m s)
      (h0 := hwp2.h0) (h1 := hwp2.h1) (h2 := hwp2.h2)
  ·
    exact toeplitzL_eq_zero_of_rows (s := s) (w := wp3At m s)
      (h0 := hwp3.h0) (h1 := hwp3.h1) (h2 := hwp3.h2)

/-- Convenience: extract just `hop_w0At` from the constructed `XiJetQuotOpZeroAtOrder`. -/
theorem hop_w0At_from_row012ConvolutionAtRevAtOrderOut
    (m : ℕ) (s : OffSeed Xi)
    (H : XiRow012ConvolutionAtRevAtOrderOut m s) :
    (toeplitzL 2 (JetQuotOp.aRk1 s) (w0At m s)) = 0 := by
  simpa using (xiJetQuotOpZeroAtOrder_of_row012ConvolutionAtRevAtOrderOut (m := m) (s := s) H).hop_w0At

/-
If you want an *instance* that typeclass-search can find, you need some upstream
instance producing `XiRow012ConvolutionAtRevAtOrderOut m s`.

Your repo provides a theorem-level producer:
  `xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic : XiRow012ConvolutionAtRevAtOrderOut m s`
in `...FromTrueAnalytic.lean` (Rec2-gated). If you import it, you can define:

instance (m : ℕ) (s : OffSeed Xi) : XiJetQuotOpZeroAtOrder m s := by
  classical
  exact xiJetQuotOpZeroAtOrder_of_row012ConvolutionAtRevAtOrderOut (m := m) (s := s)
    (xiRow012ConvolutionAtRevAtOrderOut_trueAnalytic (m := m) (s := s))

I’m leaving this commented to keep this helper purely “wiring”, not “source choosing”.
-/

end XiPacket
end Targets
end Hyperlocal

end
