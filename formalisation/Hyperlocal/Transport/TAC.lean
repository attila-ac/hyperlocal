/-
  Hyperlocal/Transport/TAC.lean

  TAC bridge: parity projector (oddPart) → prime-indexed sine witness
  κ * sin(t * log p). Keeps the arithmetic bottleneck isolated.
-/

import Hyperlocal.Cancellation.PrimeWitness
import Hyperlocal.Cancellation.PrimeWitnessParity

noncomputable section

namespace Hyperlocal
namespace Transport
namespace TAC

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness

/-- Local shorthand to avoid collision with `_root_.Even` (numeric evenness). -/
abbrev EvenF (f : ℝ → ℝ) : Prop :=
  Hyperlocal.Cancellation.PrimeWitness.Even f

/-- Prime-specialized trig test with phase length `log p`. -/
def PhiPrime (A B C : ℝ → ℝ) (p : ℕ) : ℝ → ℝ :=
  fun t => PhiABC A B C (Real.log (p : ℝ)) t

/--
Parity projector + prime phase:
If A,B,C are even then the odd part of the prime-specialized trig test
is purely sine with phase `t * log p`.
-/
theorem oddPart_PhiPrime
    {A B C : ℝ → ℝ} {p : ℕ}
    (hA : EvenF A) (hB : EvenF B) (hC : EvenF C) :
    ∀ t, oddPart (PhiPrime A B C p) t
        = C t * Real.sin (t * Real.log (p : ℝ)) := by
  intro t
  -- unfold PhiPrime and apply the existing parity bridge theorem
  simpa [PhiPrime, EvenF] using
    (oddPart_PhiABC (A := A) (B := B) (C := C)
      (L := Real.log (p : ℝ)) hA hB hC t)

/--
Constant-coefficient specialization:
If C(t)=κ (constant), then the odd part is exactly PhiShape κ t p.
-/
theorem oddPart_PhiPrime_constC
    {A B : ℝ → ℝ} {κ : ℝ} {p : ℕ}
    (hA : EvenF A) (hB : EvenF B) :
    ∀ t, oddPart (PhiPrime A B (fun _ => κ) p) t
        = PhiShape κ t p := by
  intro t
  have hC : EvenF (fun _ : ℝ => κ) := by
    intro u
    simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
  -- use oddPart_PhiPrime and then unfold PhiShape
  simpa [PhiShape] using
    (oddPart_PhiPrime (A := A) (B := B) (C := fun _ => κ)
      (p := p) hA hB hC t)

/--
End-to-end TAC → finite prime witness (2 or 3).

If the TAC scalar test has trig form PhiABC with even A,B and constant sine coefficient κ,
then for κ≠0 and t≠0, the odd-part scalar cannot vanish at both p=2 and p=3.
-/
theorem tac_finite_prime_witness_2_3
    {A B : ℝ → ℝ} {κ t : ℝ}
    (hA : EvenF A) (hB : EvenF B)
    (hκ : κ ≠ 0) (ht : t ≠ 0) :
    oddPart (PhiPrime A B (fun _ => κ) 2) t ≠ 0 ∨
    oddPart (PhiPrime A B (fun _ => κ) 3) t ≠ 0 := by
  -- rewrite both oddParts into PhiShape
  have h2 :
      oddPart (PhiPrime A B (fun _ => κ) 2) t = PhiShape κ t 2 :=
    oddPart_PhiPrime_constC (A := A) (B := B) (κ := κ) (p := 2) hA hB t
  have h3 :
      oddPart (PhiPrime A B (fun _ => κ) 3) t = PhiShape κ t 3 :=
    oddPart_PhiPrime_constC (A := A) (B := B) (κ := κ) (p := 3) hA hB t

  have hw : PhiShape κ t 2 ≠ 0 ∨ PhiShape κ t 3 ≠ 0 :=
    Hyperlocal.Cancellation.PrimeWitness.finite_prime_witness_2_3
      (κ := κ) (t := t) hκ ht

  cases hw with
  | inl hPhi2 =>
      left
      simpa [h2] using hPhi2
  | inr hPhi3 =>
      right
      simpa [h3] using hPhi3

end TAC
end Transport
end Hyperlocal
