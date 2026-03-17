import Hyperlocal.Targets.XiFinalRhCorridorProvider
import Hyperlocal.Targets.XiWp5JetPacketEqOnResonantBranchProvider
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets

namespace TAC
open Hyperlocal.Targets.XiPacket.TAC
end TAC

open Hyperlocal.Targets.XiPacket
open scoped Real

/--
Installed sharp resonant packet-equality provider from an explicit theorem input.

This packages the last naked local theorem gate

  wpAt 0 s 5 = w0At 0 s

on the exact `log(3/2)` resonant branch into the standard provider class.
-/
instance instXiWp5JetPacketEqOnResonantBranchProviderInstalled
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    XiWp5JetPacketEqOnResonantBranchProvider where
  wp5_jetPacketEq_on_resonant_branch := hpack_res

/--
Bundled final RH corridor installed from the single sharp resonant packet-equality
theorem gate.

This is strictly sharper than installing from the wp5 row-0 theorem: the only live
local burden is now the packet transport identity itself.
-/
instance instXiFinalRhCorridorProviderInstalledFromResonantJetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    XiFinalRhCorridorProvider := by
  letI : XiWp5JetPacketEqOnResonantBranchProvider :=
    instXiWp5JetPacketEqOnResonantBranchProviderInstalled
      (hpack_res := hpack_res)
  infer_instance

end Targets
end Hyperlocal
