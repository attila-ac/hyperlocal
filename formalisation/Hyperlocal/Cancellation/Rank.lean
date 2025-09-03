/-
Rank: “full rank” via ker = ⊥ for the diagonal toy map.

This file wraps `applyM` as a ℂ-linear map on `Jet6` and shows:
  * ker (applyM_lin A t) = ⊥   if all diagonal weights are ≠ 0
  * hence range = ⊤ (surjectivity form of “full rank”)
  * and a dimension-form statement of full rank
-/

import Hyperlocal.Cancellation.Solo
import Hyperlocal.Cancellation.Setup   -- for A₀, t₀, diag_nonzero_at_rho'
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
open Complex

namespace Hyperlocal
namespace Cancellation

/-- Recall: `Jet6 = Fin 6 → ℂ`. -/
abbrev Jet6 := Fin 6 → ℂ

/-- Package the functional map `applyM` as a ℂ-linear map. -/
def applyM_lin (A t : ℝ) : Jet6 →ₗ[ℂ] Jet6 :=
{ toFun := applyM A t,
  map_add' := by
    intro x y; ext i; simp [applyM, mul_add],
  map_smul' := by
    intro a x; ext i; simp [applyM, mul_left_comm, mul_assoc] }

/-- Kernel is trivial when all diagonal entries are nonzero (linear-map version). -/
lemma ker_applyM_lin_bot
    (A t : ℝ)
    (h : ∀ i : Fin 6, diagScale A t i ≠ 0) :
    (applyM_lin A t).ker = ⊥ := by
  ext x; constructor
  · intro hx
    -- `hx : x ∈ ker` means `applyM_lin A t x = 0`.
    have hx0 : applyM A t x = 0 := by
      simpa using (LinearMap.mem_ker.mp hx)
    -- Use your pointwise elimination lemma.
    have : x = 0 := kernel_trivial A t h hx0
    simpa [this]
  · intro hx
    -- Elements of ⊥ are exactly `0`, which are always in the kernel.
    rcases Submodule.mem_bot.mp hx with rfl
    simp [LinearMap.mem_ker, applyM_lin, applyM]

/-- “Full rank” in surjectivity form: `range = ⊤`. -/
lemma range_applyM_lin_top
    (A t : ℝ)
    (h : ∀ i : Fin 6, diagScale A t i ≠ 0) :
    (applyM_lin A t).range = ⊤ := by
  classical
  -- On equal finite-dim spaces, `ker = ⊥ ↔ range = ⊤`.
  have hker : (applyM_lin A t).ker = ⊥ := ker_applyM_lin_bot A t h
  simpa using
    (LinearMap.ker_eq_bot_iff_range_eq_top (applyM_lin A t)).1 hker

/-- Dimension-theoretic “full rank”: `finrank (range f) = finrank V`. -/
lemma finrank_range_eq_finrank
    (A t : ℝ)
    (h : ∀ i : Fin 6, diagScale A t i ≠ 0) :
    FiniteDimensional.finrank ℂ (LinearMap.range (applyM_lin A t)) =
    FiniteDimensional.finrank ℂ (Jet6) := by
  classical
  -- From the dimension theorem: finrank(range) + finrank(ker) = finrank(V).
  have hsum := (applyM_lin A t).finrank_range_add_finrank_ker
  -- Our ker is ⊥, so its finrank is 0.
  have hker0 : FiniteDimensional.finrank ℂ (LinearMap.ker (applyM_lin A t)) = 0 := by
    simpa [ker_applyM_lin_bot A t h] using
      (Submodule.finrank_bot : FiniteDimensional.finrank ℂ (⊥ : Submodule ℂ Jet6) = 0)
  -- Rearranging the equality gives finrank(range) = finrank(V).
  -- (all ranks are Nats, so add_right_cancel works)
  exact Nat.add_right_cancel (hsum.trans (by simp [hker0]))

/-- Specialization at the canonical test point `(A₀, t₀) = (-1/2, 1)`. -/
theorem applyM_full_rank_at_rho' :
    (applyM_lin A₀ t₀).ker = ⊥ ∧ (applyM_lin A₀ t₀).range = ⊤ := by
  refine ⟨ker_applyM_lin_bot A₀ t₀ diag_nonzero_at_rho', ?_⟩
  simpa using range_applyM_lin_top A₀ t₀ diag_nonzero_at_rho'

end Cancellation
end Hyperlocal
end
