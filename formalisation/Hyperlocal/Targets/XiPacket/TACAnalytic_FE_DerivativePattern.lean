/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_FE_DerivativePattern.lean

  FE derivative pattern:
  If H z = H (1 - z), then
    iteratedDeriv n H z = (-1)^n * iteratedDeriv n H (1 - z).
-/

import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace TAC

/-- FE symmetry: `H z = H (1 - z)`. -/
def FunFE (H : ℂ → ℂ) : Prop := ∀ z : ℂ, H z = H (1 - z)

/-- The affine involution `z ↦ 1 - z`.  (NO `[simp]` to avoid simp loops.) -/
def oneMinus (z : ℂ) : ℂ := (1 : ℂ) - z

lemma oneMinus_eq (z : ℂ) : oneMinus z = (1 : ℂ) - z := rfl

theorem iteratedDeriv_eq_pow_neg_one_mul_oneMinus
    (H : ℂ → ℂ) (hFE : FunFE H) :
    ∀ n : ℕ, ∀ z : ℂ,
      iteratedDeriv n H z = ((-1 : ℂ) ^ n) * iteratedDeriv n H (oneMinus z) := by
  intro n z

  -- Pointwise FE as a function equality (avoid simp rewriting).
  have hfun : (fun t : ℂ => H t) = (fun t : ℂ => H (oneMinus t)) := by
    funext t
    -- FE: H t = H (1 - t)
    simpa [FunFE, oneMinus] using (hFE t)

  -- Lift FE through iteratedDeriv via congrArg (NO simp).
  have hfun_iter : iteratedDeriv n H = iteratedDeriv n (fun t : ℂ => H (oneMinus t)) := by
    simpa using congrArg (fun f : (ℂ → ℂ) => iteratedDeriv n f) hfun

  have hL : iteratedDeriv n H z = iteratedDeriv n (fun t : ℂ => H (oneMinus t)) z := by
    simpa using congrArg (fun F : (ℂ → ℂ) => F z) hfun_iter

  -- Now compute iteratedDeriv of (t ↦ H(1 - t)) using shift + neg.
  let f1 : ℂ → ℂ := fun x => H ((1 : ℂ) + x)

  have h_comp : (fun t : ℂ => H (oneMinus t)) = (fun t : ℂ => f1 (-t)) := by
    funext t
    -- 1 - t = 1 + (-t)
    simp [f1, oneMinus, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]

  have h_neg :
      iteratedDeriv n (fun t : ℂ => f1 (-t)) z
        = ((-1 : ℂ) ^ n) • iteratedDeriv n f1 (-z) := by
    simpa using (iteratedDeriv_comp_neg (n := n) (f := f1) (a := z))

  have h_shift :
      iteratedDeriv n f1 = (fun t : ℂ => iteratedDeriv n H ((1 : ℂ) + t)) := by
    simpa [f1] using (iteratedDeriv_comp_const_add (n := n) (f := H) (s := (1 : ℂ)))

  have h_shift_eval :
      iteratedDeriv n f1 (-z) = iteratedDeriv n H ((1 : ℂ) + (-z)) := by
    simpa using congrArg (fun F : (ℂ → ℂ) => F (-z)) h_shift

  -- Finish, converting • to * at the end.
  calc
    iteratedDeriv n H z
        = iteratedDeriv n (fun t : ℂ => H (oneMinus t)) z := hL
    _   = iteratedDeriv n (fun t : ℂ => f1 (-t)) z := by
          -- rewrite the *function* argument, not by simp
          simpa using congrArg (fun g : (ℂ → ℂ) => iteratedDeriv n g z) h_comp
    _   = ((-1 : ℂ) ^ n) • iteratedDeriv n f1 (-z) := h_neg
    _   = ((-1 : ℂ) ^ n) • iteratedDeriv n H ((1 : ℂ) + (-z)) := by
          simpa [h_shift_eval]
    _   = ((-1 : ℂ) ^ n) * iteratedDeriv n H (oneMinus z) := by
          -- 1 + (-z) = 1 - z, and • = *
          simp [oneMinus, sub_eq_add_neg, smul_eq_mul]

end TAC
end XiPacket
end Targets
end Hyperlocal
