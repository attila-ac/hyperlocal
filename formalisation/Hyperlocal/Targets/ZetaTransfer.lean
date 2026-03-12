/-
  Hyperlocal/Targets/ZetaTransfer.lean

  Discharge the ζ→ξ transfer step in Mathlib terms.

  UPDATED (after switching `Hyperlocal.xi` to the entire extension):
      xi(s) := s * (s - 1) * completedRiemannZeta₀ s + 1.

  With Mathlib’s lemma
      riemannZeta s = completedRiemannZeta s / Gammaℝ s  (for s ≠ 0),
  plus the fact that `Gammaℝ` does not vanish off the real axis, we get:

      ζ(ρ)=0 and ρ.im ≠ 0  ⇒  completedRiemannZeta(ρ)=0.

  Then use
      completedRiemannZeta_eq :
        completedRiemannZeta s = completedRiemannZeta₀ s - 1/s - 1/(1-s)

  to deduce
      completedRiemannZeta₀(ρ) = 1/ρ + 1/(1-ρ),
  and finally
      xi(ρ)=ρ(ρ-1) * (1/ρ + 1/(1-ρ)) + 1 = 0
  by field algebra (under `ρ ≠ 0` and `ρ ≠ 1`).

  Then we keep the same “NoOffSeed ξ ⇒ NoOffSeed ζ” bridge as before.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.RiemannZeta
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Conclusion.OffSeedToTAC
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace ZetaTransfer

open scoped Real
open Hyperlocal.Conclusion.OffSeedToTAC
open Complex

/-- Notation: ζ target from Mathlib (via `Hyperlocal.Targets.RiemannZeta`). -/
abbrev Zeta : ℂ → ℂ := Hyperlocal.zeta

/-- Notation: ξ target from this project (via `Hyperlocal.Targets.RiemannXi`). -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Off the real axis, ζ(ρ)=0 ⇒ ξ(ρ)=0 (completion factors do not kill zeros). -/
theorem xi_eq_zero_of_zeta_eq_zero_of_im_ne_zero {ρ : ℂ} :
    Zeta ρ = 0 → ρ.im ≠ 0 → Xi ρ = 0 := by
  intro hζ hIm

  -- `ρ ≠ 0` follows from `ρ.im ≠ 0`.
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hIm
    simp [h0]

  -- Also `ρ ≠ 1` follows from `ρ.im ≠ 0`.
  have hρ1 : ρ ≠ 1 := by
    intro h1
    apply hIm
    simp [h1]

  -- Rewrite ζ in terms of the completion.
  have hdiv : completedRiemannZeta ρ / ρ.Gammaℝ = 0 := by
    simpa [Zeta, Hyperlocal.zeta, riemannZeta_def_of_ne_zero hρ0] using hζ

  -- Gammaℝ has no zeros off the real axis (a zero would force `ρ` real).
  have hGamma : ρ.Gammaℝ ≠ 0 := by
    intro hG
    rcases (Complex.Gammaℝ_eq_zero_iff).1 hG with ⟨n, hn⟩
    have him0 : ρ.im = 0 := by
      have := congrArg Complex.im hn
      simpa using this
    exact hIm him0

  -- Conclude the numerator vanishes: completedRiemannZeta ρ = 0.
  have hnum : completedRiemannZeta ρ = 0 := by
    rcases (div_eq_zero_iff).1 hdiv with hnum0 | hG0
    · exact hnum0
    · exfalso
      exact hGamma hG0

  -- Use `completedRiemannZeta_eq` to solve for Λ₀(ρ).
  have hΛ0_eq : completedRiemannZeta₀ ρ = (1 / ρ) + (1 / (1 - ρ)) := by
    -- From: 0 = Λ₀ ρ - 1/ρ - 1/(1-ρ)
    have hEq0 :
        (0 : ℂ) = completedRiemannZeta₀ ρ - 1 / ρ - 1 / (1 - ρ) := by
      simpa [hnum] using (completedRiemannZeta_eq (s := ρ))
    -- Add (1/ρ + 1/(1-ρ)) to both sides and simplify.
    have hEq1 :=
      congrArg (fun t : ℂ => t + (1 / ρ + 1 / (1 - ρ))) hEq0
    -- Now simplify to isolate `completedRiemannZeta₀ ρ`.
    -- We keep `simp` conservative and finish with `ring_nf`.
    -- (No `linarith` over ℂ.)
    -- After simp: left becomes (1/ρ + 1/(1-ρ)); right becomes Λ₀ ρ.
    -- Then swap sides.
    have : (1 / ρ + 1 / (1 - ρ)) = completedRiemannZeta₀ ρ := by
      -- normalize the RHS expression
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hEq1
    simpa [eq_comm] using this

  -- Finally, show xi(ρ)=0 by algebra with `hΛ0_eq`.
  delta Xi
  delta Hyperlocal.xi
  -- Goal: ρ * (ρ - 1) * Λ₀ ρ + 1 = 0
  -- Substitute Λ₀ ρ and clear denominators (ρ ≠ 0, ρ ≠ 1).
  -- We will also need `1 - ρ ≠ 0`, i.e. `ρ ≠ 1`.
  have h1m : (1 - ρ) ≠ 0 := by
    intro h
    have : ρ = 1 := by
      -- `sub_eq_zero.mp h : (1:ℂ) = ρ`
      simpa [eq_comm] using (sub_eq_zero.mp h)
    exact hρ1 this

  -- Substitute and clear denominators.
  -- `field_simp` will use `hρ0` and `h1m`.
  -- After clearing, `ring` closes.
  simp [hΛ0_eq, div_eq_mul_inv] at *
  field_simp [hρ0, h1m]
  ring

/-- Map an off-seed of ζ to an off-seed of ξ (same ρ, same off-critical witnesses). -/
def offSeed_xi_of_offSeed_zeta (s : Hyperlocal.OffSeed Zeta) : Hyperlocal.OffSeed Xi :=
{ ρ  := s.ρ
  hρ := xi_eq_zero_of_zeta_eq_zero_of_im_ne_zero (ρ := s.ρ) s.hρ s.ht
  hσ := s.hσ
  ht := s.ht }

/-- Main transfer: NoOffSeed ξ ⇒ NoOffSeed ζ. -/
theorem noOffSeed_zeta_of_noOffSeed_xi
    (hxi : NoOffSeed Xi) : NoOffSeed Zeta := by
  intro hz
  apply hxi
  rcases hz with ⟨s⟩
  exact ⟨offSeed_xi_of_offSeed_zeta (s := s)⟩

/-- RH-facing pointwise form of the ζ ← ξ transfer:
every nontrivial zero of ζ lies on the critical line,
provided ξ has no off-seed zeros. -/
theorem criticalzero_zeta
    (hxi : NoOffSeed Xi) {ρ : ℂ}
    (hζ : Zeta ρ = 0) (hIm : ρ.im ≠ 0) :
    ρ.re = (1 / 2 : ℝ) := by
  by_contra hcrit
  have hz_off : Hyperlocal.OffSeed Zeta :=
    { ρ := ρ
      hρ := hζ
      hσ := hcrit
      ht := hIm }
  have hz_no : NoOffSeed Zeta := noOffSeed_zeta_of_noOffSeed_xi hxi
  exact hz_no ⟨hz_off⟩

end ZetaTransfer
end Targets
end Hyperlocal
