/-
  Hyperlocal/Targets/XiPacket/XiPrimeWitnessW1_AllPrimesFromNonresonance.lean

  First strong generic-prime W1 consequence of the current graph:

      sin(t log(3/2)) ≠ 0
        -> wpAt m s p is killed by the actual Toeplitz operator
        -> generic-prime ell-out / identity surfaces apply
        -> bCoeff(σ(s), t(s), p) = 0   for arbitrary prime index p

  This is stronger than the earlier `{2,3}` localizers:
  it uses the new generic-prime receiving-side algebra and the strengthened
  deterministic connector to push the W1 route onto arbitrary prime windows.
-/

import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Stage2ConnectorDeterministic
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_WcScalarOfDetNonzero
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceIdentityIm
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/--
Real-pivot generic-prime consequence of the current W1 nonresonant branch.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_of_kappaAt
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hk : kappaAt m s ≠ 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_p_of_row0
    (m := m) (s := s) (p := p)
    (hroute := routeA_stencil_zero_of_tval_ne_zero_atOrder
      (m := m) (s := s) htv)
    (hk := hk)
    (hwpop := by
      have hwp :
          toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p) = 0 :=
        W1.toeplitzL_aRk1_wpAt_eq_zero_of_tval_ne_zero
          (m := m) (s := s) (p := p) htv
      have h0 := congrArg (fun w => w (0 : Fin 3)) hwp
      simpa using h0)

/--
Imag-pivot generic-prime consequence of the current W1 nonresonant branch.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_of_kappaAtIm
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hk : kappaAtIm m s ≠ 0)
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  exact xiToeplitzRecurrenceIdentity_atOrder_im_p_of_row0
    (m := m) (s := s) (p := p)
    (hroute := routeA_stencil_zero_of_tval_ne_zero_atOrder
      (m := m) (s := s) htv)
    (hk := hk)
    (hwpop := by
      have hwp :
          toeplitzL 2 (JetQuotOp.aRk1 s) (wpAt m s p) = 0 :=
        W1.toeplitzL_aRk1_wpAt_eq_zero_of_tval_ne_zero
          (m := m) (s := s) (p := p) htv
      have h0 := congrArg (fun w => w (0 : Fin 3)) hwp
      simpa using h0)

/--
Pivot-gate generic-prime consequence of the current W1 nonresonant branch.

This is the strongest honest theorem surface currently supported:
assuming the present W1 nonresonant branch and the standard pivot-nonzero gate,
the proof now yields `bCoeff(...,p)=0` for arbitrary prime windows.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    [XiKappaPivotNonzero s]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  rcases xiKappaPivotNonzero_out (s := s) with hRe | hIm
  · rcases hRe with ⟨m, hk⟩
    exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAt
      (m := m) (s := s) (p := p) (hk := hk) (htv := htv)
  · rcases hIm with ⟨m, hk⟩
    exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAtIm
      (m := m) (s := s) (p := p) (hk := hk) (htv := htv)

end XiPacket
end Targets
end Hyperlocal
