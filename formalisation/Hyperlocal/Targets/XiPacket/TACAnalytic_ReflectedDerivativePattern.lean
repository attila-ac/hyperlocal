/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_ReflectedDerivativePattern.lean
  Analytic content: Reflected derivative patterns for FE-satisfying functions.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open Complex

/-- Snapshot-robust iterated complex derivative operator. -/
def cderivIter : ℕ → (ℂ → ℂ) → (ℂ → ℂ)
  | 0,     f => f
  | n + 1, f => cderivIter n (fun z => deriv f z)

@[simp] lemma cderivIter_zero (f : ℂ → ℂ) : cderivIter 0 f = f := rfl
@[simp] lemma cderivIter_succ (n : ℕ) (f : ℂ → ℂ) :
    cderivIter (n+1) f = cderivIter n (fun z => deriv f z) := rfl

/-- Convenient point-連結 notation. -/
abbrev cderivIterAt (n : ℕ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  cderivIter n f z

/-- The affine reflection map `z ↦ 1 - z` has derivative `-1`. -/
lemma hasDerivAt_one_sub (z : ℂ) :
    HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1 : ℂ) z := by
  simpa using (hasDerivAt_const z (1 : ℂ)).sub (hasDerivAt_id z)

/--
Signed FE → signed FE for derivatives.
If `F z = c * F (1 - z)`, then `deriv F z = (-c) * deriv F (1 - z)`.
-/
lemma deriv_signed_reflect
    {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    (c : ℂ) (hFEc : ∀ z : ℂ, F z = c * F (1 - z)) (z : ℂ) :
    deriv F z = (-c) * deriv F (1 - z) := by
  let G : ℂ → ℂ := fun w => c * F (1 - w)
  have hfun : F = G := funext (fun w => by simp [G, hFEc w])
  have hGder : deriv G z = c * (deriv F (1 - z) * (-1 : ℂ)) := by
    have hFd : HasDerivAt F (deriv F (1 - z)) (1 - z) := (hF.differentiableAt).hasDerivAt
    have href : HasDerivAt (fun w : ℂ => (1 : ℂ) - w) (-1 : ℂ) z := hasDerivAt_one_sub z
    have hcomp : HasDerivAt (fun w : ℂ => F (1 - w)) (deriv F (1 - z) * (-1 : ℂ)) z := hFd.comp z href
    simpa [G] using (hcomp.const_mul c).deriv
  calc
    deriv F z = deriv G z := by rw [hfun]
    _         = c * (deriv F (1 - z) * (-1 : ℂ)) := hGder
    _         = (-c) * deriv F (1 - z) := by ring

/-- Key definitional lemma: `cderivIter (n+1) H z = deriv (cderivIter n H) z`. -/
lemma cderivIter_succ_apply : ∀ n : ℕ, ∀ (H : ℂ → ℂ) (z : ℂ),
    cderivIter (n+1) H z = deriv (cderivIter n H) z := by
  intro n
  induction n with
  | zero => intro H z; simp [cderivIter]
  | succ n ih => intro H z; simpa [cderivIter] using (ih (fun t => deriv H t) z)

/--
FE for all iterated derivatives:
`cderivIterAt n H p = (-1)^n * cderivIterAt n H (1 - p)`.
-/
lemma cderivIterAt_reflect
    {H : ℂ → ℂ}
    (hFE : ∀ z : ℂ, H z = H (1 - z))
    (hDiffIter : ∀ n : ℕ, Differentiable ℂ (cderivIter n H)) :
    ∀ n : ℕ, ∀ p : ℂ,
      cderivIterAt n H p = ((-1 : ℂ) ^ n) * cderivIterAt n H (1 - p)
  | 0, p => by simp [cderivIterAt, hFE p]
  | n+1, p => by
      -- The recursive step needs to reference H explicitly in the IH
      have hFn_FE : ∀ z : ℂ, (cderivIter n H) z = ((-1 : ℂ) ^ n) * (cderivIter n H) (1 - z) :=
        fun z => cderivIterAt_reflect hFE hDiffIter n z

      have hder : deriv (cderivIter n H) p = (-( (-1 : ℂ) ^ n)) * deriv (cderivIter n H) (1 - p) :=
        deriv_signed_reflect (hDiffIter n) ((-1 : ℂ) ^ n) hFn_FE p

      have hsucc_p : cderivIter (n+1) H p = deriv (cderivIter n H) p :=
        cderivIter_succ_apply n H p
      have hsucc_1mp : cderivIter (n+1) H (1 - p) = deriv (cderivIter n H) (1 - p) :=
        cderivIter_succ_apply n H (1 - p)

      calc
        cderivIterAt (n+1) H p
            = deriv (cderivIter n H) p := hsucc_p
        _   = (-( (-1 : ℂ) ^ n)) * deriv (cderivIter n H) (1 - p) := hder
        _   = ((-1 : ℂ) ^ (n+1)) * cderivIter (n+1) H (1 - p) := by
                simp [pow_succ, hsucc_1mp]
        _   = ((-1 : ℂ) ^ (n+1)) * cderivIterAt (n+1) H (1 - p) := rfl

end TAC
end XiPacket
end Targets
end Hyperlocal
