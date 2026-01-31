/-
  Hyperlocal/Targets/ZetaTransfer.lean

  Discharge the ζ→ξ transfer step in Mathlib terms.

  With our target choice
      xi s := s * (s - 1) * completedRiemannZeta s
  and Mathlib’s lemma
      riemannZeta s = completedRiemannZeta s / s.Gammaℝ   (for s ≠ 0),
  plus the fact that `Gammaℝ` does not vanish off the real axis, we get:

      ζ(ρ)=0 and ρ.im ≠ 0  ⇒  ξ(ρ)=0.

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

  -- Conclude the numerator vanishes.
  have hnum : completedRiemannZeta ρ = 0 := by
    rcases (div_eq_zero_iff).1 hdiv with hnum0 | hG0
    · exact hnum0
    · exfalso
      exact hGamma hG0

  -- Now ξ(ρ)=ρ*(ρ-1)*completedRiemannZeta(ρ)=0.
  -- `xi` is an `abbrev`, so force unfolding via `delta` (not `simp`/`rw`).
  delta Xi
  delta Hyperlocal.xi
  simp [hnum]

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

end ZetaTransfer
end Targets
end Hyperlocal
