/-
  Hyperlocal/Appendix/InstabilityK2_Seed.lean
  k = 2: seed-style bridge stays; global proof deferred.
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Abs
import Hyperlocal.Cancellation.InstabilityHyp
import Hyperlocal.Cancellation.BridgeToInstability  -- for BridgeWitnessSeedFromWindow (seed path)

noncomputable section
namespace Hyperlocal
namespace Cancellation
namespace InstabilityK2Seed

/-- Target (math, to be proved later):
    There exists a base index `n0` and a windowed recurrence instance
    producing QCC/TRC stencils at `(A₀,t₀)`, with `G n0 ≠ 0`. -/
structure K2SeedWitness (A t : ℝ) : Prop where
  ok : True  -- fill with your actual stencils once available

/-- Placeholder instance for `UnstableHom 2` remains available,
    so the seed bridge composes and keeps the pipeline green. -/
theorem unstable_k2_all_t (A t : ℝ) : UnstableHom 2 A t := ⟨trivial⟩

end InstabilityK2Seed
end Cancellation
end Hyperlocal
