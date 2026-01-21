/-
  Hyperlocal/Transport/ToeplitzInterface.lean

  Minimal Toeplitz/transport interface (lean-light, robust):

  * Window space: `Fin (n+1) → ℂ`
  * Right shift / Toeplitz transport operator `shiftR` (zero-fill)
  * Parity operator `parity` (index reversal)
  * Define left shift as the parity-conjugate of right shift:
        shiftL := parity ∘ shiftR ∘ parity
    so the “equivariance/parity” lemma becomes a one-liner.

  This avoids fragile imports/lemmas and keeps the interface minimal.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Transport

/-- A finite “window” of length `n+1` with complex entries. -/
abbrev Window (n : ℕ) : Type := Fin n → ℂ

/-- Parity / reversal on a window: `(x₀,…,xₙ) ↦ (xₙ,…,x₀)`. -/
def parity {n : ℕ} (x : Window (n + 1)) : Window (n + 1) :=
  fun i => x i.rev

/-- Parity is an involution. -/
lemma parity_parity {n : ℕ} (x : Window (n + 1)) : parity (parity x) = x := by
  funext i
  -- `Fin.rev_rev` is in Mathlib; `simp` finds it.
  simp [parity]

/--
Right shift (Toeplitz transport) with zero fill:
`(x₀,x₁,…,xₙ) ↦ (0,x₀,…,xₙ₋₁)`.
-/
def shiftR {n : ℕ} (x : Window (n + 1)) : Window (n + 1)
  | ⟨0, _⟩       => 0
  | ⟨k + 1, hk⟩  => x ⟨k, Nat.lt_of_lt_of_le (Nat.lt_of_succ_lt_succ hk) (Nat.le_succ _)⟩
/--
Left shift is defined as the parity-conjugate of `shiftR`:
`shiftL := parity ∘ shiftR ∘ parity`.

This is the cleanest way to make “parity structure” explicit with minimal proof burden.
-/
def shiftL {n : ℕ} (x : Window (n + 1)) : Window (n + 1) :=
  parity (shiftR (parity x))

/--
Equivariance / parity lemma (the one you want for the manuscript):
reversing after right-shift equals left-shift after reversing.
-/
theorem parity_shiftR_eq_shiftL_parity {n : ℕ} (x : Window (n + 1)) :
    parity (shiftR x) = shiftL (parity x) := by
  -- expand shiftL, then cancel `parity ∘ parity`.
  simp [shiftL, parity_parity]

end Transport
end Hyperlocal
