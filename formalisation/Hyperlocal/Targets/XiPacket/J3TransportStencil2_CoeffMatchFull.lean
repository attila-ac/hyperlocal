/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_CoeffMatchFull.lean
-/

import Hyperlocal.Transport.ToeplitzInterface
import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_EvalGermJet2
import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_EvalGermCoeff012
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC
namespace J3

open Complex
open scoped BigOperators
open Hyperlocal.Transport

def coeffWin (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) : Window 3 :=
  ![ coeff a δ N 0
   , coeff a δ N 1
   , coeff a δ N 2 ]

theorem coeffWin_eq_explicit_N3 (a : ℕ → ℂ) (δ : ℂ) :
    coeffWin a δ 3
      =
    ![
      a 0 + a 1 * δ + a 2 * (δ ^ 2),
      a 1 + (2 : ℂ) * a 2 * δ,
      a 2
    ] := by
  classical
  ext i
  fin_cases i
  · simp [coeffWin, coeff_eq_sum_pow, Finset.sum_range_succ, pow_two,
      add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  · simp [coeffWin, coeff_eq_sum_mul_nat_pow_pred, Finset.sum_range_succ, pow_two,
      add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]
  · simp [coeffWin, coeff_eq_sum_choose_two, Finset.sum_range_succ, pow_two,
      add_assoc, add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

theorem evalTrunc_eq_jet2_explicit_N3 (a : ℕ → ℂ) (δ : ℂ) :
    evalTrunc a δ 3
      =
    jet2
      (a 0 + a 1 * δ + a 2 * (δ ^ 2))
      (a 1 + (2 : ℂ) * a 2 * δ)
      (a 2) := by
  classical
  have h0 := evalTrunc_eq_jet2 (a := a) (δ := δ) (N := 3)

  have hw := coeffWin_eq_explicit_N3 (a := a) (δ := δ)
  have hcoeff0 :
      coeff a δ 3 0 = a 0 + a 1 * δ + a 2 * (δ ^ 2) := by
    simpa [coeffWin] using congrArg (fun w : Window 3 => w 0) hw
  have hcoeff1 :
      coeff a δ 3 1 = a 1 + (2 : ℂ) * a 2 * δ := by
    simpa [coeffWin] using congrArg (fun w : Window 3 => w 1) hw
  have hcoeff2 :
      coeff a δ 3 2 = a 2 := by
    simpa [coeffWin] using congrArg (fun w : Window 3 => w 2) hw

  calc
    evalTrunc a δ 3
        = jet2 (coeff a δ 3 0) (coeff a δ 3 1) (coeff a δ 3 2) := h0
    _   = jet2
          (a 0 + a 1 * δ + a 2 * (δ ^ 2))
          (a 1 + (2 : ℂ) * a 2 * δ)
          (a 2) := by
          rw [hcoeff0, hcoeff1, hcoeff2]

end J3
end TAC
end XiPacket
end Targets
end Hyperlocal
