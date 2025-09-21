-- Hyperlocal/Cancellation/BridgeSmoke.lean
import Hyperlocal.Cancellation.Bridge
noncomputable section
namespace Hyperlocal
namespace Cancellation

-- A compile-time check that the lemma is reachable (optional):
-- #check recurrence_of_convolution_pivot   -- or with full namespace

/-- Smoke test: expose the pivot lemma under a short wrapper so
    downstream code can `open` this file and use it directly. -/
lemma use_pivot
  -- TODO: paste the exact arguments/signature you found via grep
  : True := trivial

end Cancellation
end Hyperlocal
