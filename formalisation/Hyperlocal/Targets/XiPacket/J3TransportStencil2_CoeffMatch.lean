/-
  Hyperlocal/Targets/XiPacket/J3TransportStencil2_CoeffMatch.lean

  Step 1 (cycle-safe algebraic core):
  Compute the length-3 lower transport stencil explicitly.

  This lemma is the deterministic “(1, δ, δ^2/2)” Toeplitz/transport statement that
  later gets paired with:
    * evalTrunc_eq_jet2
    * EvalGermCoeff012 closed forms
  to prove coefficient-extraction agrees with transport in the J3 model.
-/

import Hyperlocal.Transport
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_XiTransportCompat
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

open scoped BigOperators

/--
Algebraic stencil expansion at length 3:

`transportLower 3 δ w` equals the window obtained by applying the truncated Taylor-shift
weights `(1, δ, δ^2/2)` to the base window `w`.

This is *purely finite algebra* and is the cycle-safe core of Step 1.
-/
theorem transportLower3_eq_stencil
    (δ : ℂ) (w : Window 3) :
    TAC.transportLower 3 δ w
      =
    ![
      w 0,
      (w 1) + δ * (w 0),
      (w 2) + δ * (w 1) + (δ ^ 2) / (2 : ℂ) * (w 0)
    ] := by
  classical

  -- mulVec is definitional: avoid Matrix.dotProduct entirely
  have mulVec_eq_sum {n : Type} [Fintype n] [DecidableEq n]
      (M : Matrix n n ℂ) (v : n → ℂ) (i : n) :
      M.mulVec v i = ∑ j : n, M i j * v j := by
    rfl

  -- expand a Fin 3 sum into three terms
  have sum_fin3 {α : Type} [AddCommMonoid α] (f : Fin 3 → α) :
      (∑ j : Fin 3, f j) = f 0 + f 1 + f 2 := by
    classical
    have h1 : (∑ j : Fin 3, f j) = f 0 + ∑ j : Fin 2, f j.succ := by
      simpa using (Fin.sum_univ_succ (n := 2) f)
    have h2 : (∑ j : Fin 2, f j.succ) = f 1 + f 2 := by
      let g : Fin 2 → α := fun j => f j.succ
      simpa [g] using (Fin.sum_univ_succ (n := 1) g)
    simpa [h2, add_assoc] using h1

  ext i
  fin_cases i
  · -- i = 0
    -- Only diagonal term survives after transpose: coefficient = 1
    simp [TAC.transportLower, mulVec_eq_sum, Matrix.transpose, sum_fin3, transportMat,
      div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  · -- i = 1
    -- terms j=0,1 survive: coeffs δ, 1
    simp [TAC.transportLower, mulVec_eq_sum, Matrix.transpose, sum_fin3, transportMat,
      div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]
  · -- i = 2
    -- terms j=0,1,2 survive: coeffs δ^2/2, δ, 1
    simp [TAC.transportLower, mulVec_eq_sum, Matrix.transpose, sum_fin3, transportMat,
      div_eq_mul_inv, pow_two, mul_assoc, mul_left_comm, mul_comm,
      add_assoc, add_left_comm, add_comm]

end TAC

end XiPacket
end Targets
end Hyperlocal
