/-
  Hyperlocal/Targets/Stage3SystemXi.lean

  Target-focused Stage–3 goal file.

  Purpose:
    1) State the exact remaining Stage–3 obligation for the target ξ-function:
         Stage3System Xi   (where Xi := Hyperlocal.xi)
    2) Provide immediate downstream consequences as lemmas taking
       `hs : Stage3System Xi` as input (so the file builds green without faking).
    3) Include a “field order template” (commented) showing precisely what data
       must be constructed to prove `Stage3System Xi`.

  This file is intended to be the single place where the real analytic/operator
  work lands (transport → extraction for ξ), replacing the hypothesis `hs`.
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Conclusion.Stage3BridgeOfStage3System
import Hyperlocal.Conclusion.OffSeedToTAC

noncomputable section

namespace Hyperlocal
namespace Targets

open scoped Real

/-
IMPORTANT:
Lean’s notation/quotation precheck can be finicky with the single-token notation `ξ`.
So this file avoids using the notation token and instead fixes the target function
as a local abbrev `Xi`.
-/

/-- The target ξ-function, in a notation-free, scope-stable form. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- The Stage–3 goal, stated explicitly for the target ξ (here: `Xi`). -/
abbrev Stage3Goal : Prop :=
  Hyperlocal.Transport.Stage3System (H := Xi)

/--
If we had `Stage3System Xi`, the existing glue immediately yields `NoOffSeed Xi`.

This compiles green and is the exact endgame dependency you want:
the only missing input is `hs : Stage3System Xi`.
-/
theorem noOffSeed_xi_of_stage3System
    (hs : Hyperlocal.Transport.Stage3System (H := Xi)) :
    Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed (H := Xi) := by
  -- Lemma is defined in Hyperlocal/Conclusion/Stage3BridgeOfStage3System.lean
  exact Hyperlocal.Conclusion.noOffSeed_of_stage3System (H := Xi) hs

/-
========================
FIELD-ORDER TEMPLATE
========================

To prove `Stage3System Xi`, you must construct an inhabitant of
`Hyperlocal.Transport.Stage3SystemData Xi` and then wrap it into `Nonempty`.

Required fields (in the order Lean expects):

  sys : Hyperlocal.Transport.Stage3SystemData (H := Xi) where
    test   : Hyperlocal.OffSeed Xi → (ℕ → ℝ → ℝ)
    tac    : Hyperlocal.OffSeed Xi → Hyperlocal.Transport.TACData
    hMatch : ∀ (s) (p) (t),
      test s p t =
        Hyperlocal.Transport.TAC.PhiPrime
          (tac s).A (tac s).B (fun _ => (tac s).κ) p t
    hOdd2  : ∀ s, oddPart (test s 2) s.ρ.im = 0
    hOdd3  : ∀ s, oddPart (test s 3) s.ρ.im = 0

Then:

  have : Hyperlocal.Transport.Stage3System (H := Xi) := ⟨⟨sys⟩⟩

So the real work is exactly:
  - define `test s p t` from transported symmetry / truncated jet / Toeplitz machinery,
  - extract A,B,κ with κ≠0 and evenness proofs hA,hB,
  - prove the matching equation hMatch,
  - prove the two oddPart vanishings at p=2 and p=3.

When ready, replace the hypothesis in `noOffSeed_xi_of_stage3System` by:

  theorem stage3System_xi : Hyperlocal.Transport.Stage3System (H := Xi) := by
    refine ⟨⟨{ test := ?_, tac := ?_, hMatch := ?_, hOdd2 := ?_, hOdd3 := ?_ }⟩⟩

and discharge each subgoal.
-/

end Targets
end Hyperlocal
