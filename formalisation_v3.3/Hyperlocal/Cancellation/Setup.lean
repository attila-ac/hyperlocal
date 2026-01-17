import Hyperlocal.Cancellation.Solo
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

noncomputable section
namespace Hyperlocal
namespace Cancellation

open Complex

/-- Canonical test parameters: `A₀ = -1/2`, `t₀ = 1`. -/
def A₀ : ℝ := - (1 / 2 : ℝ)
def t₀ : ℝ := 1

/-- Entrywise nonvanishing of the toy diagonal at `(A₀,t₀)`. -/
lemma diag_nonzero_at_rho' : ∀ i : Fin 6, diagScale A₀ t₀ i ≠ 0 := by
  -- real identity we’ll reuse: 1 - 2*A₀ = 2
  have hAℝ : 1 - 2 * A₀ = (2 : ℝ) := by
    norm_num [A₀]
  -- move that identity to ℂ
  have hAℂ : ((1 - 2 * A₀ : ℝ) : ℂ) ≠ 0 := by
    simpa [hAℝ] using (by norm_num : ((2 : ℝ) : ℂ) ≠ (0 : ℂ))
  -- tiny nonzero facts
  have hI  : (I : ℂ) ≠ 0 := by simpa using Complex.I_ne_zero
  have h2C : (2 : ℂ) ≠ 0 := by norm_num
  have h2I : (2 : ℂ) * I ≠ 0 := mul_ne_zero h2C hI
  intro i
  -- case split on i = 0..5
  fin_cases i <;>
  first
    -- i = 0,4,5 : weight is 1
    | simp [diagScale, A₀, t₀]
    -- i = 1 : weight is 2*I
    | simpa [diagScale, A₀, t₀, mul_comm, mul_left_comm, mul_assoc] using h2I
    -- i = 2 : weight is 1 - 2*A₀ = 2 (in ℂ)
    | simpa [diagScale, A₀, t₀] using hAℂ
    -- i = 3 : weight is (2*I) * (1 - 2*A₀) and both factors are ≠ 0
    | have : ((2 : ℂ) * I) * ((1 - 2 * A₀ : ℝ) : ℂ) ≠ 0 :=
        mul_ne_zero h2I hAℂ
      simpa [diagScale, A₀, t₀, mul_comm, mul_left_comm, mul_assoc] using this

/-- Specialization of `kernel_trivial` at `(A₀,t₀)`. -/
theorem kernel_trivial_at_rho'
    {x : Jet6} (hx : applyM A₀ t₀ x = 0) : x = 0 :=
  kernel_trivial A₀ t₀ diag_nonzero_at_rho' hx

end Cancellation
end Hyperlocal
end
