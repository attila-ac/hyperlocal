/-
  Hyperlocal/Targets/XiPacket/XiRouteA_PivotEliminationLe2.lean

  Task D (Plan C++J): Stage–3 anchor robustness, elimination lemma.

  From:
    * a quotient-jet statement at the anchor `z = s.ρ`,
    * three coordinate equalities w0=w1=w2=0,

  derive a contradiction using bounded nonflatness at the anchor
    `routeA_nonflat_le2_z_w0`.

  Snapshot-robust: use `cderivIter := deriv^[m]` (XiWindowJetPivotDefs).
-/

import Hyperlocal.Targets.XiPacket.XiRouteA_PivotNonflatLe2
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs  -- `cderivIter`
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport

namespace TAC

/--
If `w` is a genuine 3-jet of `routeA_G s` at `s.ρ` and its first three coords vanish,
this contradicts bounded nonflatness (≤2) at that anchor.
-/
theorem false_of_isJet3AtOrderQuot_and_coords_zero
    (m : ℕ) (s : OffSeed Xi) (w : Window 3)
    (Hjet : IsJet3AtOrderQuot m s (s.ρ) w)
    (Hw0 : w 0 = 0) (Hw1 : w 1 = 0) (Hw2 : w 2 = 0) :
    False := by
  classical

  -- `Hjet` is an And-chain in your env:
  --   w 0 = f ∧ w 1 = deriv f ∧ w 2 = deriv (deriv f)
  have hw0' : w 0 = (routeA_G s) (s.ρ) := Hjet.1
  have hw1' : w 1 = deriv (routeA_G s) (s.ρ) := Hjet.2.1
  have hw2' : w 2 = deriv (deriv (routeA_G s)) (s.ρ) := Hjet.2.2

  -- Hence the three derivatives (orders 0,1,2) vanish.
  have h0 : (routeA_G s) (s.ρ) = 0 := by
    simpa [hw0'] using Hw0
  have h1 : deriv (routeA_G s) (s.ρ) = 0 := by
    simpa [hw1'] using Hw1
  have h2 : deriv (deriv (routeA_G s)) (s.ρ) = 0 := by
    simpa [hw2'] using Hw2

  -- Turn those into `cderivIter` equalities.
  have hc0 : cderivIter 0 (routeA_G s) (s.ρ) = 0 := by
    simpa [cderivIter] using h0
  have hc1 : cderivIter 1 (routeA_G s) (s.ρ) = 0 := by
    -- `deriv^[1] f = deriv f`
    simpa [cderivIter] using h1
  have hc2 : cderivIter 2 (routeA_G s) (s.ρ) = 0 := by
    -- `deriv^[2] f = deriv (deriv f)`
    simpa [cderivIter, Function.iterate_succ] using h2

  -- Contradict bounded nonflatness (≤2) at `s.ρ`.
  rcases routeA_nonflat_le2_z_w0 (s := s) with ⟨k, hk⟩
  fin_cases k
  · exact hk (by simpa using hc0)
  · exact hk (by simpa using hc1)
  · exact hk (by simpa using hc2)

end TAC

end XiPacket
end Targets
end Hyperlocal
