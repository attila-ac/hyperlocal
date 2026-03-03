/-
  Hyperlocal/Targets/XiPacket/XiOrbitGeometry.lean

  Orbit geometry & quartet-polynomial permutation facts only.

  No analytic content.
  No removable lemmas.
  No EntireFun.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Hyperlocal.Factorization

import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Factorization

/-- `ρ ≠ conj ρ` for an off-seed (imag part nonzero). -/
lemma offSeed_ne_conj (s : OffSeed xi) : s.ρ ≠ (starRingEnd ℂ) s.ρ := by
  intro h
  have himEq : s.ρ.im = ((starRingEnd ℂ) s.ρ).im := congrArg Complex.im h
  -- `im (conj z) = - im z`
  have : s.ρ.im = - s.ρ.im := by simpa using himEq
  have : s.ρ.im = 0 := by linarith
  exact s.ht this

lemma offSeed_conj_ne (s : OffSeed xi) : (starRingEnd ℂ) s.ρ ≠ s.ρ := by
  simpa [eq_comm] using offSeed_ne_conj s

/-- `ρ ≠ oneMinus ρ` for an off-seed (not on the critical line). -/
lemma offSeed_ne_oneMinus (s : OffSeed xi) : s.ρ ≠ oneMinus s.ρ := by
  intro h
  have hRe : s.ρ.re = (oneMinus s.ρ).re := congrArg Complex.re h
  have hRe' : s.ρ.re = 1 - s.ρ.re := by
    simpa [Hyperlocal.oneMinus] using hRe
  have hre : s.ρ.re = (1 / 2 : ℝ) := by linarith
  exact s.hσ hre

lemma offSeed_oneMinus_ne (s : OffSeed xi) : oneMinus s.ρ ≠ s.ρ := by
  simpa [eq_comm] using offSeed_ne_oneMinus s

/-- `ρ ≠ oneMinus (conj ρ)` for an off-seed (also critical line contradiction). -/
lemma offSeed_ne_oneMinus_conj (s : OffSeed xi) : s.ρ ≠ oneMinus ((starRingEnd ℂ) s.ρ) := by
  intro h
  have hRe : s.ρ.re = (oneMinus ((starRingEnd ℂ) s.ρ)).re := congrArg Complex.re h
  have hRe' : s.ρ.re = 1 - s.ρ.re := by
    -- `re (conj z) = re z`
    simpa [Hyperlocal.oneMinus] using hRe
  have hre : s.ρ.re = (1 / 2 : ℝ) := by linarith
  exact s.hσ hre

lemma offSeed_oneMinus_conj_ne (s : OffSeed xi) :
    oneMinus ((starRingEnd ℂ) s.ρ) ≠ s.ρ := by
  simpa [eq_comm] using offSeed_ne_oneMinus_conj s

/-- `oneMinus (conj ρ) ≠ conj ρ` for off-seed (critical line contradiction). -/
lemma offSeed_oneMinus_conj_ne_conj (s : OffSeed xi) :
    oneMinus ((starRingEnd ℂ) s.ρ) ≠ (starRingEnd ℂ) s.ρ := by
  intro h
  have hRe : (oneMinus ((starRingEnd ℂ) s.ρ)).re = ((starRingEnd ℂ) s.ρ).re :=
    congrArg Complex.re h
  have : 1 - s.ρ.re = s.ρ.re := by
    simpa [Hyperlocal.oneMinus] using hRe
  have hre : s.ρ.re = (1 / 2 : ℝ) := by linarith
  exact s.hσ hre

/-- `oneMinus (conj ρ) ≠ oneMinus ρ` for off-seed (injectivity forces `conj ρ = ρ`). -/
lemma offSeed_oneMinus_conj_ne_oneMinus (s : OffSeed xi) :
    oneMinus ((starRingEnd ℂ) s.ρ) ≠ oneMinus s.ρ := by
  intro h
  have : (starRingEnd ℂ) s.ρ = s.ρ := by
    -- cancel `oneMinus` by applying `fun z => (1:ℂ) - z` to both sides
    have := congrArg (fun z : ℂ => (1 : ℂ) - z) h
    simpa [Hyperlocal.oneMinus, sub_sub, add_comm, add_left_comm, add_assoc] using this
  exact offSeed_ne_conj s (by simpa [eq_comm] using this)

/-- Convenience: flipped orientation of `offSeed_oneMinus_conj_ne_oneMinus`. -/
lemma offSeed_oneMinus_ne_oneMinus_conj (s : OffSeed xi) :
    oneMinus s.ρ ≠ oneMinus ((starRingEnd ℂ) s.ρ) := by
  simpa [eq_comm] using offSeed_oneMinus_conj_ne_oneMinus s

/-! Quartet polynomial permutation facts -/

lemma Rρk_conj_eq (ρ : ℂ) (k : ℕ) :
    Factorization.Rρk ((starRingEnd ℂ) ρ) k = Factorization.Rρk ρ k := by
  -- this is just orbit invariance of the quartet polynomial
  simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
    Hyperlocal.oneMinus, mul_comm, mul_left_comm, mul_assoc,
    star_one, star_sub, star_star]

lemma Rρk_oneMinus_eq (ρ : ℂ) (k : ℕ) :
    Factorization.Rρk (oneMinus ρ) k = Factorization.Rρk ρ k := by
  simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
    Hyperlocal.oneMinus, mul_comm, mul_left_comm, mul_assoc]

lemma Rρk_oneMinus_conj_eq (ρ : ℂ) (k : ℕ) :
    Factorization.Rρk (oneMinus ((starRingEnd ℂ) ρ)) k = Factorization.Rρk ρ k := by
  simp [Factorization.Rρk, Hyperlocal.MinimalModel.quartetPolyPow,
    Hyperlocal.oneMinus, mul_comm, mul_left_comm, mul_assoc,
    star_one, star_sub, star_star]

end XiPacket
end Targets
end Hyperlocal
