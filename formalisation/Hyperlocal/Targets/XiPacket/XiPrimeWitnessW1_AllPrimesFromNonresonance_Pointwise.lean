import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_AllPrimesFromNonresonance
import Hyperlocal.Targets.XiPacket.XiDslopeToKappaAtOrder
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
Pointwise generic-prime consequence of the current W1 nonresonant branch,
without requiring the typeclass pivot gate.

This is the local no-class version of
`bCoeff_eq_zero_of_tval_ne_zero`, obtained by manufacturing the needed
pivot order `m` from the dslope nonflatness witness at the chosen off-seed.
-/
theorem bCoeff_eq_zero_of_tval_ne_zero_pointwise
    (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (p : ℝ) = 0 := by
  classical

  let m : ℕ := Classical.choose (xiJetNonflat_dslope_exists (s := s))
  have hmDs : XiPacket.dslopeIterAt (m := m) (s := s) ≠ 0 :=
    Classical.choose_spec (xiJetNonflat_dslope_exists (s := s))

  have hKap :
      (Transport.kappa (reVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
        ∨
      (Transport.kappa (imVec3 (w0At m s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0) :=
    hkappaAt_of_dslopeIter_ne0 (m := m) (s := s) hmDs

  cases hKap with
  | inl hRe =>
      exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAt
        (m := m) (s := s) (p := p) (hk := hRe) (htv := htv)
  | inr hIm =>
      exact bCoeff_eq_zero_of_tval_ne_zero_of_kappaAtIm
        (m := m) (s := s) (p := p) (hk := hIm) (htv := htv)

/-- Prime-2 specialization of the previous pointwise theorem. -/
theorem bCoeff2_eq_zero_of_tval_ne_zero_pointwise
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (2 : ℝ) = 0 := by
  exact bCoeff_eq_zero_of_tval_ne_zero_pointwise
    (s := s) (p := 2) (htv := htv)

/-- Prime-3 specialization of the previous pointwise theorem. -/
theorem bCoeff3_eq_zero_of_tval_ne_zero_pointwise
    (s : Hyperlocal.OffSeed Xi)
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (htv :
      ((Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) : ℝ) : ℂ) ≠ 0) :
    bCoeff (σ s) (t s) (3 : ℝ) = 0 := by
  exact bCoeff_eq_zero_of_tval_ne_zero_pointwise
    (s := s) (p := 3) (htv := htv)

end XiPacket
end Targets
end Hyperlocal
