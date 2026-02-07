/-
  Hyperlocal/Targets/XiPacket/XiLemmaCToTACZeros2_3.lean

  Phase 5 (Plan C++):
  PURE glue (no ξ-semantic proofs).

  Goal:
    From `XiLemmaC s` (the Phase-4.5 semantic cliff bundle),
    produce the exact `OffSeedTACZeros2_3 Xi` witness package:

      ∃ A B κ, EvenF A ∧ EvenF B ∧ κ ≠ 0 ∧
        oddPart (PhiPrime A B (fun _ => κ) 2) t0 = 0 ∧
        oddPart (PhiPrime A B (fun _ => κ) 3) t0 = 0

  Strategy:
    XiLemmaC s
      ⟹ WindowPayload (via `xiWindowPayload`)
      ⟹ ∃ κ ≠ 0 ∧ sin(t0 log 2)=0 ∧ sin(t0 log 3)=0 (via WindowPayloadFacts)
      ⟹ choose A=B=0 and use `oddPart_PhiPrime_constC` + `PhiShape = κ*sin(...)`.
-/

import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Targets.XiPacket.XiWindowLemmaC
import Hyperlocal.Targets.XiPacket.WindowPayloadFacts
import Mathlib.Tactic

noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real

open Hyperlocal.Transport
open Hyperlocal.Transport.TAC
open Hyperlocal.Cancellation.PrimeWitness

/--
Phase-5 local trigger:
from `XiLemmaC s` produce the `OffSeedTACZeros2_3` witness triple (A,B,κ)
for this particular off-seed `s`.
-/
theorem xi_TACZeros2_3_of_XiLemmaC
    (s : Hyperlocal.OffSeed Xi) (hC : XiLemmaC s) :
    ∃ (A B : ℝ → ℝ) (κ : ℝ),
      EvenF A ∧ EvenF B ∧ κ ≠ 0 ∧
        oddPart (PhiPrime A B (fun _ => κ) 2) s.ρ.im = 0 ∧
        oddPart (PhiPrime A B (fun _ => κ) 3) s.ρ.im = 0 := by
  -- Phase 4.5 → Phase 4 payload.
  have X : WindowPayload s.ρ.re s.ρ.im := xiWindowPayload (s := s) hC

  -- Payload → κ ≠ 0 and the two sine locks.
  rcases WindowPayload.exists_kappa_sinlog2_sinlog3 (X := X) with
    ⟨κ, hkappa, hsin2, hsin3⟩

  -- Choose the simplest even functions A=B=0.
  refine ⟨(fun _ : ℝ => (0 : ℝ)), (fun _ : ℝ => (0 : ℝ)), κ, ?_, ?_, hkappa, ?_, ?_⟩
  · simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
  · simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]

  · -- p = 2
    have hA : EvenF (fun _ : ℝ => (0 : ℝ)) := by
      simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
    have hB : EvenF (fun _ : ℝ => (0 : ℝ)) := by
      simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
    calc
      oddPart (PhiPrime (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ => κ) 2) s.ρ.im
          = Hyperlocal.Cancellation.PrimeWitness.PhiShape κ s.ρ.im 2 := by
              simpa using
                (oddPart_PhiPrime_constC
                  (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 0)
                  (κ := κ) (p := 2) (hA := hA) (hB := hB) (t := s.ρ.im))
      _ = 0 := by
              simp [Hyperlocal.Cancellation.PrimeWitness.PhiShape, hsin2]

  · -- p = 3
    have hA : EvenF (fun _ : ℝ => (0 : ℝ)) := by
      simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
    have hB : EvenF (fun _ : ℝ => (0 : ℝ)) := by
      simp [EvenF, Hyperlocal.Cancellation.PrimeWitness.Even]
    calc
      oddPart (PhiPrime (fun _ : ℝ => 0) (fun _ : ℝ => 0) (fun _ => κ) 3) s.ρ.im
          = Hyperlocal.Cancellation.PrimeWitness.PhiShape κ s.ρ.im 3 := by
              simpa using
                (oddPart_PhiPrime_constC
                  (A := fun _ : ℝ => 0) (B := fun _ : ℝ => 0)
                  (κ := κ) (p := 3) (hA := hA) (hB := hB) (t := s.ρ.im))
      _ = 0 := by
              simp [Hyperlocal.Cancellation.PrimeWitness.PhiShape, hsin3]

/--
Phase-5 global wrapper:
if later you prove `∀ s, XiLemmaC s`, this immediately yields `OffSeedTACZeros2_3 Xi`.
-/
theorem xi_offSeedTACZeros2_3_of_XiLemmaC
    (hC : ∀ s : Hyperlocal.OffSeed Xi, XiLemmaC s) :
    Hyperlocal.Transport.OffSeedTACZeros2_3 Xi := by
  intro s
  rcases xi_TACZeros2_3_of_XiLemmaC (s := s) (hC := hC s) with
    ⟨A, B, κ, hA, hB, hk, h2, h3⟩
  exact ⟨A, B, κ, hA, hB, hk, h2, h3⟩

end XiPacket
end Targets
end Hyperlocal
