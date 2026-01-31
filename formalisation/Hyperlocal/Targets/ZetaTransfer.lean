/-
  Hyperlocal/Targets/ZetaTransfer.lean

  Bridge: NoOffSeed ξ  →  NoOffSeed ζ

  The only “semantic” analytic input needed is the completion-factor lemma:
    ζ(ρ)=0 and ρ.im ≠ 0  ⇒  ξ(ρ)=0.

  This file keeps that as ONE isolated axiom for now (exactly like XiPhaseLock),
  so everything downstream stays green and stable.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Targets.RiemannZeta
import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Conclusion.OffSeedToTAC

noncomputable section

namespace Hyperlocal
namespace Targets
namespace ZetaTransfer

open Hyperlocal.Conclusion.OffSeedToTAC

/-- Notation: ξ target already fixed in your project. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Notation: ζ target from Mathlib (via `Hyperlocal.Targets.RiemannZeta`). -/
abbrev Zeta : ℂ → ℂ := Hyperlocal.zeta

/--
THE analytic “completion factor is nonzero off the real axis” lemma.

Replace this axiom with the real Mathlib proof once you decide the cleanest lemma path.
-/
axiom xi_eq_zero_of_zeta_eq_zero_of_im_ne_zero {ρ : ℂ} :
  Zeta ρ = 0 → ρ.im ≠ 0 → Xi ρ = 0

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
