import Hyperlocal.Transport.TACExtraction
import Hyperlocal.Conclusion.Stage3BridgeOfStage3System
import Hyperlocal.Conclusion.OffSeedToTAC

#check Hyperlocal.Transport.Stage3System
#check Hyperlocal.Transport.OffSeedTACZeros2_3
#check Hyperlocal.Transport.offSeedTACZeros2_3_of_stage3System

namespace Scratch
variable {H : ℂ → ℂ}

-- Find the finisher lemma by TYPE (no guessing the name / namespace)
#find _ : (Hyperlocal.Transport.Stage3System H →
          Hyperlocal.Conclusion.OffSeedToTAC.NoOffSeed H)

end Scratch
