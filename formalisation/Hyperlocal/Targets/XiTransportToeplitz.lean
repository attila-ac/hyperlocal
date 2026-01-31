/-
  Hyperlocal/Targets/XiTransportToeplitz.lean

  “One missing identification lemma” isolated cleanly:

    IsToeplitz XiTransportOp n s  :=  ∃ coeffs, XiTransportOp n s = toeplitzR n coeffs

  Once you prove THAT for your concrete XiTransportOp, everything else is one-liners:
    • shift-generated/stencil form (ShiftGenerated)
    • parity intertwining (parityₗ ∘ T = Tleft ∘ parityₗ)

  This file contains NO axioms and NO sorries:
  it only proves consequences from the identification hypothesis.
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.TACToeplitz
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiTransport

open Hyperlocal.Transport

/-- Notation-free target name (matches Stage3SystemXi.lean style). -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- The Toeplitz normal-form property (THIS is the identification lemma you must prove). -/
def IsToeplitz
    (XiTransportOp : (n : ℕ) → Hyperlocal.OffSeed Xi → EndW n)
    (n : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop :=
  ∃ coeffs : ℕ → ℂ, XiTransportOp n s = toeplitzR n coeffs

/-- Consequence 1: Toeplitz normal form ⇒ shift-generated (“stencil”). -/
theorem shiftGenerated_of_isToeplitz
    (XiTransportOp : (n : ℕ) → Hyperlocal.OffSeed Xi → EndW n)
    {n : ℕ} {s : Hyperlocal.OffSeed Xi}
    (hT : IsToeplitz (XiTransportOp := XiTransportOp) n s) :
    ShiftGenerated n (shiftRₗ n) (XiTransportOp n s) := by
  rcases hT with ⟨coeffs, h⟩
  simpa [h] using (toeplitzR_shiftGenerated (n := n) (coeffs := coeffs))

/-- Consequence 2: Toeplitz normal form ⇒ explicit parity intertwining. -/
theorem parityₗ_comp_of_isToeplitz
    (XiTransportOp : (n : ℕ) → Hyperlocal.OffSeed Xi → EndW n)
    {n : ℕ} {s : Hyperlocal.OffSeed Xi}
    (hT : IsToeplitz (XiTransportOp := XiTransportOp) n s) :
    ∃ coeffs : ℕ → ℂ,
      (parityₗ n).comp (XiTransportOp n s)
        = (toeplitzL n coeffs).comp (parityₗ n) := by
  rcases hT with ⟨coeffs, h⟩
  refine ⟨coeffs, ?_⟩
  simpa [h] using (parityₗ_comp_toeplitzR (n := n) (coeffs := coeffs))

end XiTransport
end Targets
end Hyperlocal
