/-
  Hyperlocal/Conclusion/Finisher.lean

  The only missing ingredient for an unconditional RH conclusion is the
  bridge: an off-critical seed produces an UnstableHom instance.
-/
import Hyperlocal.Manuscript.All

namespace Hyperlocal
namespace Conclusion

-- Whatever the “off-critical seed” datatype is (or will be):
structure OffSeed where
  k : ℕ
  A t : ℝ
  -- plus the hypotheses actually needed from the analytic side

-- The *single* remaining bridge obligation:
axiom offSeed_to_unstable : ∀ s : OffSeed, Hyperlocal.Cancellation.UnstableHom s.k s.A s.t
-- (Keep as axiom only temporarily; later replace by a real proof and delete.)

theorem no_offSeed : ¬ (∃ s : OffSeed, True) := by
  intro h
  rcases h with ⟨s, _⟩
  have : Hyperlocal.Cancellation.UnstableHom s.k s.A s.t := offSeed_to_unstable s
  -- now use your established pipeline:
  -- exact Hyperlocal.no_cancellation_if_unstable (k:=s.k) (A:=s.A) (t:=s.t)
  --   (…BridgeData…) (…combine lemma…) this
  -- The point: this file becomes the one place to “close the loop”.

end Conclusion
end Hyperlocal
