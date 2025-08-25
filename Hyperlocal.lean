import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

open Complex

variable (s : ℂ) (H : ℂ → ℂ)

axiom RC : H (conj s) = conj (H s)
axiom FE : H s = H (1 - s)

variable (ρ' : ℂ)

theorem conjugate_zero_of_zero (h_rho_is_zero : H ρ' = 0) : H (conj ρ') = 0 := by
  rw [RC]
  rw [h_rho_is_zero]
  rw [conj_zero]
