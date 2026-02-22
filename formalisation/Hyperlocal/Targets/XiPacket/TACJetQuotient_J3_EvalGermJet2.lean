/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_EvalGermJet2.lean

  Packaging lemma only: convert the `range 3` sum form into `jet2`.
  Kept in a separate file because `jet2` / quotient defs can be expensive to elaborate.

  IMPORTANT: we bump heartbeats *locally* here to avoid whnf timeouts.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_EvalGerm
import Mathlib.Tactic

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 2048

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC
namespace J3

open Complex
open scoped BigOperators

/-- Packaging lemma moved out of the Step-1 core file. -/
theorem evalTrunc_eq_jet2 (a : ℕ → ℂ) (δ : ℂ) (N : ℕ) :
    evalTrunc a δ N =
      jet2 (coeff a δ N 0) (coeff a δ N 1) (coeff a δ N 2) := by
  classical

  -- Step 1 lemma gives the `range 3` normal form.
  have h := evalTrunc_eq_sum_wdeg_two (a := a) (δ := δ) (N := N)
  rw [h]

  -- Expand the `range 3` sum *explicitly*.
  let f : ℕ → J3 := fun k => (C (coeff a δ N k)) * (w : J3) ^ k
  change (Finset.range 3).sum f = jet2 (coeff a δ N 0) (coeff a δ N 1) (coeff a δ N 2)

  -- `range 3` = {0,1,2}. Do it via `sum_range_succ` three times.
  have hr3 : (Finset.range 3).sum f = f 0 + f 1 + f 2 := by
    calc
      (Finset.range 3).sum f = (Finset.range 2).sum f + f 2 := by
        simpa using (Finset.sum_range_succ f 2)
      _ = ((Finset.range 1).sum f + f 1) + f 2 := by
        -- expand (range 2).sum and reassociate
        simpa [add_assoc] using congrArg (fun t => t + f 2) (Finset.sum_range_succ f 1)
      _ = (((Finset.range 0).sum f + f 0) + f 1) + f 2 := by
        simpa [add_assoc] using congrArg (fun t => t + f 1 + f 2) (Finset.sum_range_succ f 0)
      _ = f 0 + f 1 + f 2 := by
        simp [add_assoc]

  rw [hr3]
  dsimp [f]

  -- Now use the *safe* unfolding lemma for jet2 (you said `J3.jet2_def` exists).
  -- Keep simp tiny: only powers 0/1/2 and ring reassociation.
  simp [J3.jet2_def, pow_zero, pow_one, pow_two, mul_assoc, add_assoc, add_left_comm, add_comm]

end J3
end TAC
end XiPacket
end Targets
end Hyperlocal
