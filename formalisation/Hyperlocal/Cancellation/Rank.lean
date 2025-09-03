/-
  formalisation/Hyperlocal/Cancellation/Rank.lean

  Bundle `applyM` as a ℂ-linear map and show that its kernel is ⊥
  under the same nonvanishing hypothesis you already proved in Setup.lean.
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.Solo    -- Jet6, diagScale, applyM, kernel_trivial
import Hyperlocal.Cancellation.Setup   -- A₀, t₀, diag_nonzero_at_rho'

noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

/-- `applyM` packaged as a ℂ-linear map on `Jet6`. -/
def applyM_lin (A t : ℝ) : Jet6 →ₗ[ℂ] Jet6 where
  toFun x := fun i => diagScale A t i * x i
  map_add' x y := by
    ext i; simp [mul_add]
  map_smul' c x := by
    ext i
    -- goal: diagScale A t i * (c * x i) = c * (diagScale A t i * x i)
    calc
      diagScale A t i * (c * x i)
          = (diagScale A t i * c) * x i := by simpa [mul_assoc]
      _   = (c * diagScale A t i) * x i := by simpa [mul_comm]
      _   = c * (diagScale A t i * x i) := by simpa [mul_assoc]

@[simp] lemma applyM_lin_apply (A t : ℝ) (x : Jet6) :
    applyM_lin A t x = applyM A t x := rfl

/-- If every diagonal weight is nonzero, then `ker (applyM_lin A t) = ⊥`. -/
lemma ker_applyM_lin_bot (A t : ℝ)
    (h : ∀ i : Fin 6, diagScale A t i ≠ 0) :
    LinearMap.ker (applyM_lin A t) = ⊥ := by
  apply le_antisymm
  · -- `ker ≤ ⊥`: any vector in the kernel is zero (use `kernel_trivial`).
    intro x hx
    have hx0 : applyM A t x = 0 := by
      simpa [LinearMap.mem_ker, applyM_lin_apply] using hx
    have : x = 0 := kernel_trivial A t h hx0
    simpa [Submodule.mem_bot] using this
  · exact bot_le  -- `⊥ ≤ ker` always.

/-- Specialization at the canonical test point `(A₀,t₀) = (-1/2, 1)`. -/
lemma ker_applyM_lin_bot_at_rho' :
    LinearMap.ker (applyM_lin A₀ t₀) = ⊥ :=
  ker_applyM_lin_bot A₀ t₀ diag_nonzero_at_rho'

end Cancellation
end Hyperlocal
