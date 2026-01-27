/-
  Hyperlocal/Transport/TACToeplitz.lean

  Manuscript-facing instantiation:
  Toeplitz/transport operators on finite windows are *finite polynomials in the shift*.

  We wrap `shiftCombo` as `toeplitzR/toeplitzL` and export:
    • ShiftGenerated witnesses (by definition),
    • the explicit parity intertwining lemma:
        parityₗ ∘ toeplitzR(coeffs) = toeplitzL(coeffs) ∘ parityₗ.
-/

import Hyperlocal.Transport.ToeplitzShiftGenerated

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped BigOperators

/-- Manuscript name: right/forward Toeplitz operator on windows (finite polynomial in `shiftRₗ`). -/
def toeplitzR (n : ℕ) (coeffs : ℕ → ℂ) : EndW n :=
  shiftCombo n (shiftRₗ n) coeffs

/-- Manuscript name: left/backward Toeplitz operator (same coefficients, built from `shiftLₗ`). -/
def toeplitzL (n : ℕ) (coeffs : ℕ → ℂ) : EndW n :=
  shiftCombo n (shiftLₗ n) coeffs

/-- Trivial “this specific operator is shift-generated” witness (by definition). -/
theorem toeplitzR_shiftGenerated (n : ℕ) (coeffs : ℕ → ℂ) :
    ShiftGenerated n (shiftRₗ n) (toeplitzR n coeffs) :=
  ⟨coeffs, rfl⟩

theorem toeplitzL_shiftGenerated (n : ℕ) (coeffs : ℕ → ℂ) :
    ShiftGenerated n (shiftLₗ n) (toeplitzL n coeffs) :=
  ⟨coeffs, rfl⟩

/-- **Key Stage–3 citeable lemma** (explicit version):
    parity conjugates the right shift polynomial into the left shift polynomial. -/
theorem parityₗ_comp_toeplitzR (n : ℕ) (coeffs : ℕ → ℂ) :
  (parityₗ n).comp (toeplitzR n coeffs) = (toeplitzL n coeffs).comp (parityₗ n) := by
  classical
  apply LinearMap.ext
  intro x
  -- Expand to a finite sum on both sides.
  simp [toeplitzR, toeplitzL, shiftCombo, LinearMap.comp_apply]
  -- Now rewrite term-by-term using the power-transport lemma.
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hkWin :
      parity ((compPow (shiftRₗ n) k) x) =
        (compPow (shiftLₗ n) k) (parity x) := by
    -- Use the linear-map lemma at the point `x`.
    have hLin := parityₗ_comp_compPow_shiftRₗ (n := n) (k := k)
    have hApp := congrArg (fun T : EndW n => T x) hLin
    -- Unpack parityₗ and composition at the Window level.
    simpa [LinearMap.comp_apply, parityₗ_apply] using hApp
  -- Scale both sides by coeffs k.
  simpa using congrArg (fun w : Window (n + 1) => (coeffs k) • w) hkWin

/- Optional aliases if you want the file name to match the narrative. -/
abbrev TACToeplitzR := toeplitzR
abbrev TACToeplitzL := toeplitzL

theorem parityₗ_comp_TACToeplitzR (n : ℕ) (coeffs : ℕ → ℂ) :
  (parityₗ n).comp (TACToeplitzR n coeffs) = (TACToeplitzL n coeffs).comp (parityₗ n) := by
  simpa [TACToeplitzR, TACToeplitzL] using
    parityₗ_comp_toeplitzR (n := n) (coeffs := coeffs)

end Transport
end Hyperlocal
