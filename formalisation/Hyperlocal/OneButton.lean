/-
  Hyperlocal/OneButton.lean

  One-button DAG sanity check.

  Policy:
  * imports the main top-level claim surfaces
  * forces elaboration of key theorems
  * DOES NOT define new instances or new mathematics
  * includes `#find` probes so we don't guess constant names
  * once you paste the names returned by `#find`, `#print axioms` gives the true staging list
-/

import Hyperlocal.Targets.XiPhaseLock
import Hyperlocal.Targets.XiPacket.XiToeplitzRecurrenceInject
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderSigmaProviderFromRec2TrueAnalytic


-- If these imports exist in your tree, keep them; if they don't, comment them out.
-- (They were the ones that were "unknown identifier" for you because the theorem names differ,
--  but the *modules* might still exist.)
-- import Hyperlocal.Conclusion.Stage3BridgeOfStage3System
-- import Hyperlocal.Conclusion.FinisherStage3System

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/-
(0) Toeplitz injection consequences (pivot-gate only): these already compile for you.
-/
namespace Targets.XiPacket

--#check xiToeplitz_hb2_fromRecurrence
--#check xiToeplitz_hb3_fromRecurrence

end Targets.XiPacket

/-
(1) Locate the actual “NoOffSeed Xi” *constant name(s)* without guessing.

Run this file; Lean will print candidates in the infoview.
Then paste the exact constant name into a #check / #print axioms block below.
-/

-- This searches for *anything* in scope whose type is `NoOffSeed Xi`.

--#print axioms Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_of_toeplitz_row0_eq_zero
--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_w0At
--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp2At
--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_wp3At
--#print axioms Hyperlocal.Targets.XiPacket.w0At
--#print axioms Hyperlocal.Targets.XiPacket.wp2At
--#print axioms Hyperlocal.Targets.XiPacket.wp3At

--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuot_row0_w0At
--#print axioms Hyperlocal.Targets.XiPacket.row0Sigma_eq_zero_of_toeplitz_row0_eq_zero

-- #print axioms Hyperlocal.Targets.XiPacket.xiAtOrderSigmaOut_fromRow0FrontierAtOrder
-- #print axioms Hyperlocal.Targets.XiPacket.routeAJetCoordProvider_axiom

-- #check (inferInstance : Hyperlocal.Targets.XiPacket.XiAtOrderCoords01Provider)
--#print axioms (inferInstance : Hyperlocal.Targets.XiPacket.XiAtOrderCoords01Provider)

--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder_fromRecurrenceA
--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder_of_opZero
--#check Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder_fromRecurrenceA
--#check Hyperlocal.Targets.XiPacket.xiJetQuotRow0WitnessCAtOrder_of_opZero

--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzRecurrenceIdentity_atOrder
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzRecurrenceIdentity_atOrder_im
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAt_fromRecurrenceC
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_fromRecurrenceC
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzEllOutAtImRe_w0_fromRecurrenceC

#print axioms Hyperlocal.Targets.XiPacket.xiAtOrderCoords01Out_fromSigmaAndRow012TrueAnalytic
#check (inferInstance : Hyperlocal.Targets.XiPacket.XiAtOrderCoords01Provider)
#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotRow012AtOrder_analytic_upstream
#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi
#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi

--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb2_fromRecurrence
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitz_hb3_fromRecurrence
--#print axioms Hyperlocal.Targets.XiPacket.xiToeplitzRecurrenceIdentity_p

--#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
--#print axioms Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
--#print axioms Hyperlocal.Targets.XiPacket.hkappaAt_of_dslopeIter_ne0
--#check Hyperlocal.Targets.XiPacket.xiBcoeff2_eq_zero
--#check Hyperlocal.Targets.XiPacket.xiBcoeff3_eq_zero
--#check Hyperlocal.Targets.XiPacket.hkappaAt_of_dslopeIter_ne0

--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder
--#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi


--#print axioms Hyperlocal.Targets.XiPacket.xiJetQuotOpZeroAtOrder
--#print axioms Hyperlocal.Targets.OffSeedPhaseLockXiPayloadAtOrder.offSeedPhaseLock_Xi

--#print axioms Hyperlocal.Targets.offSeedPhaseLock_Xi
--#print axioms Hyperlocal.Targets.noOffSeed_Xi
-- #print axioms Hyperlocal.Targets.noOffSeed_Xi
-- #print axioms Hyperlocal.Targets.noOffSeed_Zeta

-- Often there are variants like `NoOffSeed Hyperlocal.xi` or `NoOffSeed (Targets.Xi)`.
-- If the above is empty, uncomment these and see what hits:
-- #find _root_.NoOffSeed Hyperlocal.xi
-- #find _root_.NoOffSeed Targets.Xi

/-
(2) Once you see the constant name from `#find`, paste it here.

Example pattern (REPLACE the name with what `#find` shows):

#check Targets.XiPhaseLock.<FOUND_NAME>
#print axioms Targets.XiPhaseLock.<FOUND_NAME>

Keep this commented until you’ve pasted a real name.
-/
-- #check Targets.XiPhaseLock.<PASTE_FOUND_NoOffSeed_Xi_NAME_HERE>
-- #print axioms Targets.XiPhaseLock.<PASTE_FOUND_NoOffSeed_Xi_NAME_HERE>

/-
(3) Locate bridge theorems of the form “Stage3System Xi -> NoOffSeed Xi”.

Because the exact Stage3System type name can vary, we search more flexibly:
-/

-- Try these if the identifiers exist in your project; if they don't, they simply won't find anything.
-- (They also don’t error: `#find` is safe to keep even if it returns nothing.)
-- #find (_root_.Stage3System Xi → _root_.NoOffSeed Xi)
-- #find (Stage3System Xi → NoOffSeed Xi)

-- If your bridge lemma uses an intermediate "Finisher" structure, search for arrows ending in `NoOffSeed Xi`.

/-
(4) After you identify the bridge theorem name from the `#find` output, paste it here:

-- #check Conclusion.Stage3BridgeOfStage3System.<FOUND_BRIDGE_NAME>
-- #print axioms Conclusion.Stage3BridgeOfStage3System.<FOUND_BRIDGE_NAME>

Again: keep commented until you paste the real name.
-/
-- #check Conclusion.Stage3BridgeOfStage3System.<PASTE_FOUND_BRIDGE_NAME_HERE>
-- #print axioms Conclusion.Stage3BridgeOfStage3System.<PASTE_FOUND_BRIDGE_NAME_HERE>

end Hyperlocal
