/-
  Hyperlocal/Transport/ScalarFunctional.lean
-/

import Hyperlocal.Transport.JetWindow
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

/-- Complex-linear scalar functional on a jet window. -/
abbrev ScalarFunctional (n : ℕ) : Type :=
  JetWindow n →ₗ[ℂ] ℂ

/-- Coordinate functional: pick the `i`th coefficient of the window. -/
def coord (n : ℕ) (i : Fin (n + 1)) : ScalarFunctional n :=
{ toFun    := fun x => x i
  map_add' := by intro x y; rfl
  map_smul' := by intro a x; rfl
}

/-- Real scalarisation of a complex-linear functional. -/
def reEval {n : ℕ} (L : ScalarFunctional n) (x : JetWindow n) : ℝ :=
  (L x).re

@[simp] lemma reEval_coord (n : ℕ) (i : Fin (n + 1)) (x : JetWindow n) :
    reEval (coord n i) x = (x i).re := rfl

lemma reEval_congr {n : ℕ} (L : ScalarFunctional n) {x y : JetWindow n} (h : x = y) :
    reEval L x = reEval L y := by
  simp [reEval, h]

end Transport
end Hyperlocal
