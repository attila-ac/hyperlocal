import Mathlib

noncomputable section

namespace Hyperlocal
namespace Cancellation

open Polynomial

namespace UCE

def cayley (lam : ℂ) : ℂ := (lam + 1) / (lam - 1)
def cayleyInv (w : ℂ) : ℂ := (w + 1) / (w - 1)

def OnUnitCircle (lam : ℂ) : Prop := ‖lam‖ = (1 : ℝ)
def OnImagAxis (w : ℂ) : Prop := Complex.re w = 0

theorem cayley_onImagAxis_of_onUnitCircle {lam : ℂ} (h : OnUnitCircle lam) (h1 : lam ≠ 1) :
    OnImagAxis (cayley lam) := by
  classical
  unfold OnImagAxis cayley OnUnitCircle at *

  have hnorm : ‖lam‖ = (1 : ℝ) := h
  have hinv : lam⁻¹ = star lam := Complex.inv_eq_conj (z := lam) hnorm
  have hstar : star lam = lam⁻¹ := hinv.symm

  have h0 : lam ≠ 0 := by
    intro hz
    have : (‖lam‖ : ℝ) = 0 := by simp [hz]
    simpa [hnorm] using this

  have hsub : lam - 1 ≠ 0 := sub_ne_zero.mpr h1

  have hinvsub : lam⁻¹ - 1 ≠ 0 := by
    have hinv1 : lam⁻¹ ≠ (1 : ℂ) := by
      intro hinvEq
      have : (1 : ℂ) = lam := by
        have := congrArg (fun z : ℂ => z * lam) hinvEq
        simpa [mul_assoc, h0] using this
      exact h1 this.symm
    exact sub_ne_zero.mpr hinv1

  have hone : (1 - lam) ≠ 0 := by
    intro hzero
    have : (1 : ℂ) = lam := sub_eq_zero.mp hzero
    exact h1 this.symm

  have hstarC :
      star ((lam + 1) / (lam - 1)) = - ((lam + 1) / (lam - 1)) := by
    have hA :
        star ((lam + 1) / (lam - 1)) = (lam⁻¹ + 1) / (lam⁻¹ - 1) := by
      simp [div_eq_mul_inv, hstar]
    have hB : (lam⁻¹ + 1) / (lam⁻¹ - 1) = (lam + 1) / (1 - lam) := by
      field_simp [h0, hinvsub, hone]
      ring
    have hC : (lam + 1) / (1 - lam) = - ((lam + 1) / (lam - 1)) := by
      field_simp [hsub, hone]
      ring
    exact hA.trans (hB.trans hC)

  set z : ℂ := (lam + 1) / (lam - 1) with hz
  have hzstar : star z = -z := by
    simpa [hz] using hstarC

  have hre : Complex.re z = - Complex.re z := by
    have := congrArg Complex.re hzstar
    simp at this
    simpa using this

  have : Complex.re z = 0 := by linarith
  simpa [hz] using this


theorem cayleyInv_onUnitCircle_of_onImagAxis {w : ℂ} (h : OnImagAxis w) (h1 : w ≠ 1) :
    OnUnitCircle (cayleyInv w) := by
  classical
  unfold OnUnitCircle cayleyInv OnImagAxis at *

  set z : ℂ := (w + 1) / (w - 1) with hz

  have hstarw : star w = -w := by
    apply Complex.ext
    · simp [h]
    · simp

  have hwsub : w - 1 ≠ 0 := sub_ne_zero.mpr h1

  have hwplus : w + 1 ≠ 0 := by
    intro hw
    have hw' : w = (-1 : ℂ) := by
      simpa using (eq_neg_of_add_eq_zero_left hw)
    have : Complex.re w = (-1 : ℝ) := by simp [hw']
    linarith

  have hstarFrac : star ((w + 1) / (w - 1)) = (w - 1) / (w + 1) := by
    have hden : (-w - 1) ≠ (0 : ℂ) := by
      have : (-w - 1) = -(w + 1) := by ring
      simpa [this] using (neg_ne_zero.mpr hwplus)
    calc
      star ((w + 1) / (w - 1))
          = (star (w + 1)) / (star (w - 1)) := by
              simp [div_eq_mul_inv]
      _ = (star w + 1) / (star w - 1) := by simp
      _ = (-w + 1) / (-w - 1) := by
              simp [hstarw, sub_eq_add_neg]
      _ = (w - 1) / (w + 1) := by
              field_simp [hden, hwplus]
              ring

  have hzmul : z * star z = (1 : ℂ) := by
    have : ((w + 1) / (w - 1)) * ((w - 1) / (w + 1)) = (1 : ℂ) := by
      -- IMPORTANT: field_simp already closes this goal in your environment; do NOT add `ring` after it.
      field_simp [hwsub, hwplus]
    simpa [hz, hstarFrac] using this

  have hnormmul : ‖z‖ * ‖z‖ = (1 : ℝ) := by
    have := congrArg (fun t : ℂ => ‖t‖) hzmul
    simpa [norm_mul, norm_star] using this

  have hsq : (‖z‖ : ℝ) ^ 2 = 1 := by
    simpa [pow_two] using hnormmul

  have hnormz : ‖z‖ = (1 : ℝ) := by
    rcases (sq_eq_one_iff).1 hsq with hz1 | hzneg1
    · exact hz1
    · have : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
      linarith

  -- Final: goal is ‖(w+1)/(w-1)‖ = 1, and z is that fraction.
  simpa [hz] using hnormz


theorem cayley_left_inv {lam : ℂ} (h1 : lam ≠ 1) : cayleyInv (cayley lam) = lam := by
  unfold cayley cayleyInv
  have hsub : lam - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp [hsub]
  ring

theorem cayley_right_inv {w : ℂ} (h1 : w ≠ 1) : cayley (cayleyInv w) = w := by
  unfold cayley cayleyInv
  have hsub : w - 1 ≠ 0 := sub_ne_zero.mpr h1
  field_simp [hsub]
  ring

end UCE
end Cancellation
end Hyperlocal
