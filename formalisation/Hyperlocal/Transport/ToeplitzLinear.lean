/-
  Hyperlocal/Transport/ToeplitzLinear.lean

  Bundle parity and the simp-friendly right shift as ℂ-linear endomorphisms.

  IMPORTANT:
  We DO NOT try to prove `shiftR' = shiftR` or reuse `parity_shiftR_eq_shiftL_parity`.
  That was the source of the match-goal / synthetic-hole failures in `lake build`.

  Instead we:
    * import ToeplitzLinearStep (shiftR' + linearity lemmas)
    * bundle parity and shiftR' as `Module.End`
    * define shiftLₗ := parityₗ ∘ₗ shiftRₗ ∘ₗ parityₗ
    * prove the bundled parity lemma by simp + `parity_parity`
-/

import Hyperlocal.Transport.ToeplitzLinearStep
import Hyperlocal.Transport.ToeplitzInterface
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

/-- Convenience alias: ℂ-linear endomorphisms of the window `n+1`. -/
abbrev EndW (n : ℕ) : Type :=
  Module.End ℂ (Window (n + 1))

/-- Parity bundled as a linear endomorphism. -/
def parityₗ (n : ℕ) : EndW n :=
{ toFun    := fun x => parity x
  map_add' := by
    intro x y
    funext i
    simp [parity]
  map_smul' := by
    intro a x
    funext i
    simp [parity]
}

@[simp] lemma parityₗ_apply (n : ℕ) (x : Window (n + 1)) :
    parityₗ n x = parity x := rfl

/-- Right shift bundled as a linear endomorphism (using simp-friendly `shiftR'`). -/
def shiftRₗ (n : ℕ) : EndW n :=
{ toFun    := fun x => shiftR' (n := n) x
  map_add' := by
    intro x y
    -- proved in ToeplitzLinearStep, avoids match-goal hell
    simpa using (shiftR'_add (n := n) x y)
  map_smul' := by
    intro a x
    simpa using (shiftR'_smul (n := n) a x)
}

@[simp] lemma shiftRₗ_apply (n : ℕ) (x : Window (n + 1)) :
    shiftRₗ n x = shiftR' (n := n) x := rfl

/-- Left shift (bundled) as parity-conjugate of the right shift. -/
def shiftLₗ (n : ℕ) : EndW n :=
  (parityₗ n).comp ((shiftRₗ n).comp (parityₗ n))

/-- Bundled involution: parityₗ ∘ₗ parityₗ = id. -/
@[simp] lemma parityₗ_comp_parityₗ (n : ℕ) :
    (parityₗ n).comp (parityₗ n) = (LinearMap.id : EndW n) := by
  ext x i
  simp [parityₗ, LinearMap.comp_apply, parity_parity]

/--
Bundled parity/equivariance lemma:

`parityₗ ∘ₗ shiftRₗ = shiftLₗ ∘ₗ parityₗ`.

This is purely formal from the definition
`shiftLₗ := parityₗ ∘ₗ shiftRₗ ∘ₗ parityₗ`
and `parityₗ ∘ₗ parityₗ = id`.
-/
theorem parityₗ_comp_shiftRₗ_eq_shiftLₗ_comp_parityₗ (n : ℕ) :
    (parityₗ n).comp (shiftRₗ n) = (shiftLₗ n).comp (parityₗ n) := by
  ext x i
  simp [shiftLₗ, parityₗ, shiftRₗ, LinearMap.comp_apply, parity_parity]

end Transport
end Hyperlocal
