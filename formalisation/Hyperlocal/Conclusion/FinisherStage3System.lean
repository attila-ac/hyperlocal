/-
  Hyperlocal/Conclusion/FinisherStage3System.lean

  Variant finisher: accept the Stage-3 extraction interface (Stage3System)
  as input, and conclude NoOffSeed.

  This keeps the single remaining Stage-3 obligation explicit:
    produce Stage3System(ξ).
-/

import Hyperlocal.Conclusion.Stage3BridgeOfStage3System

noncomputable section

namespace Hyperlocal
namespace Conclusion

-- No new declarations needed; the lemma already exists:
--   Hyperlocal.Conclusion.noOffSeed_of_stage3System

end Conclusion
end Hyperlocal
