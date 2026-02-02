/-
  Hyperlocal/Transport/Stage3SystemOfTACZeros2_3.lean

  Pure glue lemma:
    OffSeedTACZeros2_3 H  ⇒  Stage3System H.
-/

import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Transport.TAC

noncomputable section

namespace Hyperlocal
namespace Transport

open scoped Real
open Hyperlocal.Cancellation.PrimeWitness (oddPart)

/--
If you can extract the TAC odd-part zeros at orders 2 and 3 for every off-seed,
then you can package a full `Stage3System`.

This is *pure glue*: it performs the classical choice bookkeeping for the
`Stage3SystemData` fields.
-/
theorem stage3System_of_offSeedTACZeros2_3
    (H : ℂ → ℂ) (h : OffSeedTACZeros2_3 H) : Stage3System H := by
  classical

  -- Choose A for each off-seed.
  let A : OffSeed H → ℝ → ℝ := fun s => Classical.choose (h s)
  have hArest :
      ∀ s : OffSeed H,
        ∃ B : ℝ → ℝ, ∃ κ : ℝ,
          TAC.EvenF (A s) ∧ TAC.EvenF B ∧ κ ≠ 0 ∧
            oddPart (TAC.PhiPrime (A s) B (fun _ => κ) 2) s.ρ.im = 0 ∧
            oddPart (TAC.PhiPrime (A s) B (fun _ => κ) 3) s.ρ.im = 0 :=
    fun s => Classical.choose_spec (h s)

  -- Choose B for each off-seed.
  let B : OffSeed H → ℝ → ℝ := fun s => Classical.choose (hArest s)
  have hBrest :
      ∀ s : OffSeed H,
        ∃ κ : ℝ,
          TAC.EvenF (A s) ∧ TAC.EvenF (B s) ∧ κ ≠ 0 ∧
            oddPart (TAC.PhiPrime (A s) (B s) (fun _ => κ) 2) s.ρ.im = 0 ∧
            oddPart (TAC.PhiPrime (A s) (B s) (fun _ => κ) 3) s.ρ.im = 0 :=
    fun s => Classical.choose_spec (hArest s)

  -- Choose κ for each off-seed.
  let κ : OffSeed H → ℝ := fun s => Classical.choose (hBrest s)
  have hκrest :
      ∀ s : OffSeed H,
        TAC.EvenF (A s) ∧ TAC.EvenF (B s) ∧ κ s ≠ 0 ∧
          oddPart (TAC.PhiPrime (A s) (B s) (fun _ => κ s) 2) s.ρ.im = 0 ∧
          oddPart (TAC.PhiPrime (A s) (B s) (fun _ => κ s) 3) s.ρ.im = 0 :=
    fun s => Classical.choose_spec (hBrest s)

  -- Package as Stage3SystemData.
  refine ⟨{
    tac := fun s =>
      ⟨A s, B s, κ s,
        (hκrest s).1,          -- EvenF (A s)
        (hκrest s).2.1,        -- EvenF (B s)
        (hκrest s).2.2.1⟩      -- κ s ≠ 0
    test := fun s p t => TAC.PhiPrime (A s) (B s) (fun _ => κ s) p t
    hMatch := by intro s p t; rfl
    hOdd2 := by intro s; exact (hκrest s).2.2.2.1
    hOdd3 := by intro s; exact (hκrest s).2.2.2.2
  }⟩

end Transport
end Hyperlocal
