import Mathlib.Data.Complex.Basic
import Hyperlocal.Cancellation.Solo      -- Jet6 style and conventions (pointwise module)
import Hyperlocal.Cancellation.Setup     -- A₀, t₀

noncomputable section
namespace Hyperlocal
namespace Cancellation

/-- A length-12 jet (first twelve Taylor coefficients). -/
abbrev Jet12 := Fin 12 → ℂ

/-
For k = 2 we reuse the same 6 weights twice.
Pattern for 6: [1, 2 i t, 1 - 2 A, (2 i t)(1 - 2 A), 1, 1]
For 12: repeat that block at indices 6..11.
-/
def diag12 (A t : ℝ) (i : Fin 12) : ℂ :=
  match i.val with
  | 0  => (1 : ℂ)
  | 1  => (2 : ℂ) * Complex.I * (t : ℂ)
  | 2  => (1 : ℂ) - (2 : ℂ) * (A : ℂ)
  | 3  => ((2 : ℂ) * Complex.I * (t : ℂ)) * ((1 : ℂ) - (2 : ℂ) * (A : ℂ))
  | 4  => (1 : ℂ)
  | 5  => (1 : ℂ)
  | 6  => (1 : ℂ)
  | 7  => (2 : ℂ) * Complex.I * (t : ℂ)
  | 8  => (1 : ℂ) - (2 : ℂ) * (A : ℂ)
  | 9  => ((2 : ℂ) * Complex.I * (t : ℂ)) * ((1 : ℂ) - (2 : ℂ) * (A : ℂ))
  | 10 => (1 : ℂ)
  | _  => (1 : ℂ)

/-- Apply the diagonal to a 12-jet. -/
def applyM12 (A t : ℝ) (x : Jet12) : Jet12 := fun i => diag12 A t i * x i

/-- If all 12 diagonal entries are nonzero, the kernel is trivial. -/
theorem kernel12_trivial
    (A t : ℝ)
    (h : ∀ i : Fin 12, diag12 A t i ≠ 0)
    {x : Jet12} (hx : applyM12 A t x = 0) :
    x = 0 := by
  ext i
  have hi : diag12 A t i * x i = 0 := (funext_iff.mp hx) i
  exact (mul_eq_zero.mp hi).resolve_left (h i)

/-- Entrywise nonvanishing at `(A₀,t₀)=(-1/2,1)`. -/
lemma diag12_nonzero_at_rho' : ∀ i : Fin 12, diag12 A₀ t₀ i ≠ 0 := by
  -- base nonzero facts we reuse
  have hI  : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
  have h2C : (2 : ℂ) ≠ 0 := by norm_num
  have ht0 : (t₀ : ℂ) ≠ 0 := by simp [t₀]       -- t₀ = 1
  have h2I   : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero h2C hI
  have h2It0 : (2 : ℂ) * Complex.I * (t₀ : ℂ) ≠ 0 := mul_ne_zero h2I ht0
  -- key nonzero real factor, now as a complex number
  have h1m2A₀_ne : ((1 : ℂ) - (2 : ℂ) * (A₀ : ℂ)) ≠ 0 := by
    simpa [A₀] using (by norm_num : (2 : ℂ) ≠ 0)

  -- now dispatch all 12 indices
  intro i
  fin_cases i <;>
  first|
    -- indices with diagonal entry = 1
    (simp [diag12, A₀, t₀])
  <;>
  try
    -- indices 1 and 7: 2 I t₀
    (simpa [diag12, A₀, t₀] using h2It0)
  <;>
  try
    -- indices 2 and 8: (1 - 2 A₀)
    (simpa [diag12, A₀, t₀] using h1m2A₀_ne)
  <;>
  -- indices 3 and 9: (2 I t₀) * (1 - 2 A₀)
  (all_goals
    (have hprod :
        ((2 : ℂ) * Complex.I * (t₀ : ℂ)) *
        ((1 : ℂ) - (2 : ℂ) * (A₀ : ℂ)) ≠ 0 :=
        mul_ne_zero h2It0 h1m2A₀_ne
     simpa [diag12, A₀, t₀, mul_comm, mul_left_comm, mul_assoc] using hprod))

/-- Specialisation: at `(A₀,t₀)` the diagonal-12 kernel is `{0}`. -/
theorem kernel12_trivial_at_rho'
    {x : Jet12} (hx : applyM12 A₀ t₀ x = 0) : x = 0 :=
  kernel12_trivial A₀ t₀ diag12_nonzero_at_rho' hx

/-- Tiny smoke: zero goes to zero. -/
@[simp] lemma applyM12_zero (A t : ℝ) : applyM12 A t (fun _ => (0 : ℂ)) = 0 := by
  funext i; simp [applyM12]

end Cancellation
end Hyperlocal
