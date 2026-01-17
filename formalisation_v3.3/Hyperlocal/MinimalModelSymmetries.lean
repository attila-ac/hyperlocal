import Mathlib.Data.Complex.Basic
import Hyperlocal.Core
import Hyperlocal.MinimalModel

noncomputable section
open Polynomial Complex

namespace Hyperlocal
namespace MinimalModel

/-- Evaluate `(X - z)^k` at `s` is `(s - z)^k`. -/
@[simp] lemma eval_linPow_local (s z : ℂ) (k : ℕ) :
    (linPow z k).eval s = (s - z) ^ k := by
  simp [linPow, lin, eval_pow]

/-- Non-`simp` rewrites to avoid loops. -/
lemma oneMinus_sub (s z : ℂ) :
    Hyperlocal.oneMinus s - z = - (s - Hyperlocal.oneMinus z) := by
  -- 1 - s - z = -(s - (1 - z))
  simp [Hyperlocal.oneMinus, sub_eq_add_neg]; ring

lemma oneMinus_sub_oneMinus (s z : ℂ) :
    Hyperlocal.oneMinus s - Hyperlocal.oneMinus z = - (s - z) := by
  -- 1 - s - (1 - z) = -(s - z)
  simp [Hyperlocal.oneMinus, sub_eq_add_neg]; ring

/-- Base product identity used in the FE pairing step:
    `(z - s) * ((1 - z) - s) = (s - z) * (s - (1 - z))`. -/
lemma pair_base_swap (s z : ℂ) :
    (z - s) * (Hyperlocal.oneMinus z - s)
      = (s - z) * (s - Hyperlocal.oneMinus z) := by
  -- rewrite both factors as *negatives* of the desired right-hand factors, then cancel signs
  have hz  : z - s = -(s - z) := by
    -- -(s - z) = -s + z = z - s
    simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  have hzo : Hyperlocal.oneMinus z - s = -(s - Hyperlocal.oneMinus z) := by
    -- (1 - z) - s = -(s - (1 - z))
    simp [Hyperlocal.oneMinus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  simpa [hz, hzo, neg_mul_neg]

/-- Pair, *unpowered*: `(1-s)-z` and `(1-s)-(1-z)` turn into minuses; two signs cancel. -/
lemma FE_pair_base (s z : ℂ) :
    (Hyperlocal.oneMinus s - z) * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus z)
      = (s - z) * (s - Hyperlocal.oneMinus z) := by
  -- from the two sign rewrites + `neg_mul_neg`
  simpa [oneMinus_sub s z, oneMinus_sub_oneMinus s z, neg_mul_neg, mul_comm]

/-- Pair, **powered**: raise `FE_pair_base` to `k` and split with `mul_pow`. -/
lemma FE_pair_pow (s z : ℂ) (k : ℕ) :
    (Hyperlocal.oneMinus s - z) ^ k * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus z) ^ k
      = (s - z) ^ k * (s - Hyperlocal.oneMinus z) ^ k := by
  -- take `k`-th powers on both sides and expand
  have := congrArg (fun t : ℂ => t ^ k) (FE_pair_base s z)
  simpa [mul_pow, mul_comm] using this

/-- **Functional equation (value level)** for the quartet minimal model: `R(1 - s) = R(s)`. -/
theorem quartetPolyPow_FE (ρ : ℂ) (k : ℕ) (s : ℂ) :
    (quartetPolyPow ρ k).eval (Hyperlocal.oneMinus s)
      = (quartetPolyPow ρ k).eval s := by
  classical
  -- One explicit expansion per side (no looping simp)
  have L :
      (quartetPolyPow ρ k).eval (Hyperlocal.oneMinus s)
        =
        (Hyperlocal.oneMinus s - ρ) ^ k
        * (Hyperlocal.oneMinus s - star ρ) ^ k
        * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus ρ) ^ k
        * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus (star ρ)) ^ k := by
    simp [quartetPolyPow, eval_mul, eval_linPow_local]
  have R :
      (quartetPolyPow ρ k).eval s
        =
        (s - ρ) ^ k
        * (s - star ρ) ^ k
        * (s - Hyperlocal.oneMinus ρ) ^ k
        * (s - Hyperlocal.oneMinus (star ρ)) ^ k := by
    simp [quartetPolyPow, eval_mul, eval_linPow_local]

  -- Two clean pair equalities (no cancellations ⇒ no disjunctions)
  have h₁ := FE_pair_pow s ρ k
  have h₂ := FE_pair_pow s (star ρ) k

  -- Regroup left as two pairs and rewrite by h₁, h₂; same regrouping shape on the right.
  -- This avoids *any* cancellation/t-case splits.
  have H :
      ((Hyperlocal.oneMinus s - ρ) ^ k * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus ρ) ^ k)
      * ((Hyperlocal.oneMinus s - star ρ) ^ k * (Hyperlocal.oneMinus s - Hyperlocal.oneMinus (star ρ)) ^ k)
      =
      ((s - ρ) ^ k * (s - Hyperlocal.oneMinus ρ) ^ k)
      * ((s - star ρ) ^ k * (s - Hyperlocal.oneMinus (star ρ)) ^ k) := by
    simpa [h₁, h₂]

  -- put both explicit expansions into that grouped shape and apply `H`
  rw [L, R]
  simpa [mul_comm, mul_left_comm, mul_assoc] using H

/-- (Optional helper kept around for reuse elsewhere.) -/
lemma FE_pair_base_swap_form (s z : ℂ) :
    (z - s) * (Hyperlocal.oneMinus z - s)
      = (s - z) * (s - Hyperlocal.oneMinus z) :=
  pair_base_swap s z

end MinimalModel
end Hyperlocal
