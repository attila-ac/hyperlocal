/-
  Hyperlocal/Conclusion/Stage3BridgeOfStage3System.lean

  Glue: Stage3System (transport→extraction interface) ⇒ Stage3Bridge (older
  TAC-trigger package) ⇒ NoOffSeed.

  This keeps the downstream finisher unchanged while allowing Stage–3 work
  to focus exclusively on instantiating Stage3System for the target H (ξ).
-/

import Hyperlocal.Conclusion.OffSeedToTAC
import Hyperlocal.Transport.TACExtraction

noncomputable section

namespace Hyperlocal
namespace Conclusion

open scoped Real

/-- Directly package the compressed extraction statement into the older bridge. -/
theorem stage3Bridge_of_offSeedTACZeros2_3
    {H : ℂ → ℂ}
    (h : Hyperlocal.Transport.OffSeedTACZeros2_3 H) :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge H := by
  refine ⟨?bridge⟩
  intro s
  rcases h s with ⟨A, B, κ, hA, hB, hκ, h2, h3⟩
  refine ⟨A, B, κ, hκ, ?_⟩
  exact ⟨hA, hB, h2, h3⟩

/-- Main glue: Stage3System ⇒ Stage3Bridge. -/
theorem stage3Bridge_of_stage3System
    {H : ℂ → ℂ}
    (hs : Hyperlocal.Transport.Stage3System H) :
    Hyperlocal.Conclusion.OffSeedToTAC.Stage3Bridge H := by
  exact stage3Bridge_of_offSeedTACZeros2_3
    (H := H)
    (Hyperlocal.Transport.offSeedTACZeros2_3_of_stage3System (H := H) hs)

/-- Convenience: Stage3System already closes the endgame via the existing finisher. -/
theorem noOffSeed_of_stage3System
    {H : ℂ → ℂ}
    (hs : Hyperlocal.Transport.Stage3System H) :
    Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed H := by
  exact Hyperlocal.Conclusion.OffSeedToTAC.no_offSeed_of_bridge
    (hb := stage3Bridge_of_stage3System (H := H) hs)

end Conclusion
end Hyperlocal
