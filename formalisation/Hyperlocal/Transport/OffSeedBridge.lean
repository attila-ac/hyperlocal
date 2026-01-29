/-
  Hyperlocal/Transport/OffSeedBridge.lean

  Stage–3 bridge (SAFE, decomposed):

  Goal:
    build `Conclusion.OffSeedToTAC.Stage3Bridge ξ`.

  Reality check:
    the current library has the whole “TAC → sine witness → (2,3) phase lock”
    endpoint formalised (PrimeWitness + TAC parity), but does NOT yet contain the
    analytic/operator-theoretic step that turns an off-critical xi-seed into the
    sine-vanishing constraints at p=2 and p=3.

  This file isolates that missing step as a *xi-scoped contract*:

      OffSeedPhaseLock H :
        ∀ off-seed s of H, ∃ κ ≠ 0, sin(t log 2)=0 ∧ sin(t log 3)=0
        where t := Im(s.ρ).

  Then we prove (in Lean, no sorry) that:

      OffSeedPhaseLock H  →  Stage3Bridge H

  by taking A=B=0 (even) and using `Transport.TAC.oddPart_PhiPrime_constC`
  to rewrite the odd parts as `κ * sin(t log p)`.

  Next task (the real mathematical work):
    provide an instance/proof of `OffSeedPhaseLock ξ` from your transported
    symmetry / truncated jet / Toeplitz layer.

  You can package exactly the assumptions you want about ξ into `XiLike H`,
  and then derive `Stage3Bridge H` and finally `NoOffSeed H`.
-/

import Hyperlocal.Conclusion.OffSeedToTAC
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped Real

/--
The *minimal missing Stage–3 contract*.

Interpretation:
  an off-critical seed forces a two-prime phase lock at p=2 and p=3,
  with a nonzero sine amplitude κ.
-/
def OffSeedPhaseLock (H : ℂ → ℂ) : Prop :=
  ∀ s : Hyperlocal.OffSeed H,
    ∃ κ : ℝ, κ ≠ 0 ∧
      Real.sin (s.ρ.im * Real.log (2 : ℝ)) = 0 ∧
      Real.sin (s.ρ.im * Real.log (3 : ℝ)) = 0

/--
Bundle the *xi-specific* hypotheses you actually want to assume/prove.

Notes:
- FE/RC are included because they are part of the “ξ-like” identity package,
  but the prime-witness endpoint does not need them directly.
- The only field that matters for Stage3Bridge is `phaseLock`.
-/
structure XiLike (H : ℂ → ℂ) : Prop :=
  (FE : ∀ s : ℂ, H s = H (Hyperlocal.oneMinus s))
  (RC : ∀ s : ℂ, H (star s) = star (H s))
  (phaseLock : OffSeedPhaseLock H)

/--
Core bridge lemma:

If an off-seed implies the (2,3) phase lock with κ≠0, then the manuscript’s
TAC trigger exists (choose A=B=0, C=κ constant), hence `Stage3Bridge H`.
-/
theorem stage3Bridge_of_phaseLock
    {H : ℂ → ℂ} (hlock : OffSeedPhaseLock H) :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge H := by
  refine ⟨?bridge⟩
  intro s
  rcases hlock s with ⟨κ, hκ, hsin2, hsin3⟩

  -- Choose trivial even A,B (both zero); keep κ as the constant sine amplitude.
  refine ⟨(fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (0 : ℝ)), κ, hκ, ?_⟩

  -- Prove the TAC_trigger conjunction.
  -- (Even A) ∧ (Even B) ∧ oddPart(...,p=2)=0 ∧ oddPart(...,p=3)=0
  classical
  have hA : Hyperlocal.Transport.TAC.EvenF (fun _ : ℝ => (0 : ℝ)) := by
    intro t
    simp [Hyperlocal.Transport.TAC.EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
  have hB : Hyperlocal.Transport.TAC.EvenF (fun _ : ℝ => (0 : ℝ)) := by
    intro t
    simp [Hyperlocal.Transport.TAC.EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]

  -- shorthand for t = Im(ρ)
  let t : ℝ := s.ρ.im

  -- oddPart at p=2 collapses to κ*sin(t log 2), hence vanishes by hsin2
  have hOdd2 :
      Hyperlocal.Cancellation.PrimeWitness.oddPart
        (Hyperlocal.Transport.TAC.PhiPrime
          (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => κ) 2) t = 0 := by
    have hRewrite :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 0)
        (κ := κ) (p := 2) hA hB t
    calc
      Hyperlocal.Cancellation.PrimeWitness.oddPart
          (Hyperlocal.Transport.TAC.PhiPrime
            (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => κ) 2) t
          = Hyperlocal.Cancellation.PrimeWitness.PhiShape κ t 2 := by
              simpa using hRewrite
      _ = 0 := by
              -- PhiShape κ t 2 = κ * sin(t * log 2)
              -- and hsin2 says sin(t * log 2) = 0.
              simp [Hyperlocal.Cancellation.PrimeWitness.PhiShape, t, hsin2]

  -- oddPart at p=3 collapses to κ*sin(t log 3), hence vanishes by hsin3
  have hOdd3 :
      Hyperlocal.Cancellation.PrimeWitness.oddPart
        (Hyperlocal.Transport.TAC.PhiPrime
          (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => κ) 3) t = 0 := by
    have hRewrite :=
      Hyperlocal.Transport.TAC.oddPart_PhiPrime_constC
        (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 0)
        (κ := κ) (p := 3) hA hB t
    calc
      Hyperlocal.Cancellation.PrimeWitness.oddPart
          (Hyperlocal.Transport.TAC.PhiPrime
            (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ : ℝ => κ) 3) t
          = Hyperlocal.Cancellation.PrimeWitness.PhiShape κ t 3 := by
              simpa using hRewrite
      _ = 0 := by
              simp [Hyperlocal.Cancellation.PrimeWitness.PhiShape, t, hsin3]

  -- Assemble TAC_trigger.
  exact ⟨hA, hB, hOdd2, hOdd3⟩

/-- Convenience: XiLike H implies Stage3Bridge H. -/
theorem stage3Bridge_of_XiLike
    {H : ℂ → ℂ} (hx : XiLike H) :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge H :=
  stage3Bridge_of_phaseLock (H := H) hx.phaseLock

/--
Optional convenience: XiLike H already closes the *no off-seed* endgame,
because Conclusion.OffSeedToTAC provides the generic contradiction wrapper.
-/
theorem noOffSeed_of_XiLike
    {H : ℂ → ℂ} (hx : XiLike H) :
    Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed H :=
  Hyperlocal.Conclusion.OffSeedToTAC.no_offSeed_of_bridge
    (hb := stage3Bridge_of_XiLike (H := H) hx)

end Transport
end Hyperlocal
