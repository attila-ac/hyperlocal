import Hyperlocal.Targets.XiWp5Row0ZeroOnResonantBranchProvider
import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Wp5Row0FromJetPacketEq
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
Sharpest currently isolated local theorem surface:

on the exact `log(3/2)` resonant branch, the prime-5 packet is already the
canonical central packet.
-/
class XiWp5JetPacketEqOnResonantBranchProvider : Prop where
  wp5_jetPacketEq_on_resonant_branch :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      wpAt 0 s 5 = w0At 0 s

/--
Consumer wrapper for the sharp resonant packet-equality provider.
-/
theorem wp5_jetPacketEq_on_resonant_branch_provided
    [XiWp5JetPacketEqOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      wpAt 0 s 5 = w0At 0 s :=
  XiWp5JetPacketEqOnResonantBranchProvider.wp5_jetPacketEq_on_resonant_branch

/--
Bridge theorem:
the sharp resonant packet-equality provider already yields the exact final
`wpAt 0 s 5` row-0 resonant-branch theorem.
-/
theorem wp5_row0_zero_on_resonant_branch_of_jetPacketEq_provider
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [XiWp5JetPacketEqOnResonantBranchProvider] :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  intro s hres
  exact Hyperlocal.Targets.XiPacket.W1.row0Sigma_wpAt5_eq_zero_of_eq_w0At
    (s := s)
    (hEq := wp5_jetPacketEq_on_resonant_branch_provided s hres)

/--
Instance bridge:
sharp resonant packet equality => exact final wp5-row0 provider.
-/
instance instXiWp5Row0ZeroOnResonantBranchProviderOfJetPacketEq
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [XiWp5JetPacketEqOnResonantBranchProvider] :
    XiWp5Row0ZeroOnResonantBranchProvider where
  wp5_row0_zero_on_resonant_branch :=
    wp5_row0_zero_on_resonant_branch_of_jetPacketEq_provider

end Targets
end Hyperlocal
