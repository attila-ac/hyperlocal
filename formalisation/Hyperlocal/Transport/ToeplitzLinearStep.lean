/-
  Hyperlocal/Transport/ToeplitzLinearStep.lean

  Micro-step: define a simp-friendly right shift `shiftR'` and prove:
    shiftR' (x + y) = shiftR' x + shiftR' y
    shiftR' (a • x) = a • shiftR' x

  No LinearMap packaging yet. This file should go green quickly.
-/

import Hyperlocal.Transport.ToeplitzInterface
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

/--
Simp-friendly right shift:
`(x₀,x₁,…,xₙ) ↦ (0,x₀,…,xₙ₋₁)`.
-/
def shiftR' {n : ℕ} (x : Window (n + 1)) : Window (n + 1) :=
  fun i => Fin.cases (motive := fun _ => ℂ) 0 (fun j : Fin n => x j.castSucc) i

@[simp] lemma shiftR'_zero {n : ℕ} (x : Window (n + 1)) :
    shiftR' (n := n) x 0 = 0 := by
  simp [shiftR']

@[simp] lemma shiftR'_succ {n : ℕ} (x : Window (n + 1)) (j : Fin n) :
    shiftR' (n := n) x j.succ = x j.castSucc := by
  simp [shiftR']

/-- Additivity of `shiftR'`. -/
lemma shiftR'_add {n : ℕ} (x y : Window (n + 1)) :
    shiftR' (n := n) (x + y) = shiftR' (n := n) x + shiftR' (n := n) y := by
  funext i
  refine Fin.cases ?h0 ?hs i
  · -- i = 0
    simp [shiftR']
  · -- i = j.succ
    intro j
    simp [shiftR']

/-- Homogeneity of `shiftR'`. -/
lemma shiftR'_smul {n : ℕ} (a : ℂ) (x : Window (n + 1)) :
    shiftR' (n := n) (a • x) = a • shiftR' (n := n) x := by
  funext i
  refine Fin.cases ?h0 ?hs i
  · -- i = 0
    simp [shiftR']
  · -- i = j.succ
    intro j
    simp [shiftR']

end Transport
end Hyperlocal
