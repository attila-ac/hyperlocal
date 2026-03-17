import Hyperlocal.Targets.XiPacket.XiPrimeWitnessW1_Wp5Row0FromJetPacketEq
import Hyperlocal.Targets.XiRow0SigmaWcZeroOnResonantBranchFromWp5Theorem
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
Single live local theorem node.

Direct honest attack surface:
replace the circular pair-{2,5} scalar split by the sharper jet-packet transport
equality on the exact resonant branch

  wpAt 0 s 5 = w0At 0 s.

This kills the fake local scalar subgoals and exposes the actual remaining local
mathematics.
-/
theorem wp5_row0_zero_on_resonant_branch_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wpAt 0 s 5) = 0 := by
  intro s hres
  exact XiPacket.W1.row0Sigma_wpAt5_eq_zero_of_eq_w0At
    (s := s)
    (hEq := hpack_res s hres)

/--
Canonical final blocker theorem in the sharp `wc` lane.
Everything downstream is already packaged from this statement.
-/
theorem row0Sigma_wc_zero_on_resonant_branch_closed
    [XiJetQuotRec2AtOrderTrueAnalytic]
    [TAC.XiJetWindowEqAtOrderQuotProvider]
    [RouteAWcScalarProvider]
    (hpack_res :
      ∀ s : Hyperlocal.OffSeed Xi,
        Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
        wpAt 0 s 5 = w0At 0 s) :
    ∀ s : Hyperlocal.OffSeed Xi,
      Real.sin ((t s) * Real.log ((3 : ℝ) / (2 : ℝ))) = 0 →
      row0Sigma s (wc s) = 0 := by
  exact row0Sigma_wc_zero_on_resonant_branch_of_wp5_theorem
    (hwp5_res :=
      wp5_row0_zero_on_resonant_branch_closed
        (hpack_res := hpack_res))

end Targets
end Hyperlocal
