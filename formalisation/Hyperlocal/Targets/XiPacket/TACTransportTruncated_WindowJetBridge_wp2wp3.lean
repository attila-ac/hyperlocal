/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_WindowJetBridge_wp2wp3.lean

  Cycle-safe bridge for the prime windows `wp2At` and `wp3At`.

  DESIGN:
  * no Row0 semantics / extractor imports
  * no analytic claims
  * isolate semantic content behind ONE knob per window:
      `JetShiftExact_wp2At` and `JetShiftExact_wp3At`
  * output form is `IsJet3At ... (wp2At m s)` / `IsJet3At ... (wp3At m s)`
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiPacket.XiJet3Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Complex
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

namespace TAC

/-
  Definitional unfolders (purely to make downstream rewriting painless).
-/

@[simp] theorem wp2At_def (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp2At m s = wpAt m s 2 := by
  rfl

@[simp] theorem wp3At_def (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp3At m s = wpAt m s 3 := by
  rfl

/-
  === Semantic knobs ===

  For `wp2At/wp3At` we do NOT pretend they are just transport of a jet:
  they are `w0At + a*wc + b*ws`.

  So the correct “bridge statement” is simply: the resulting window is a genuine
  3-jet of `Xi` at the intended anchor point.

  (You can later discharge these from the quotient-model Taylor identity plus
  the FE/RC and whatever analytic inputs you use to define the prime windows.)
-/

/-- Single semantic assumption for the `p=2` prime window at order `m`. -/
class JetShiftExact_wp2At (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  shift0 :
    wp2At m s 0 = Xi ((starRingEnd ℂ) s.ρ)
  shift1 :
    wp2At m s 1 = deriv Xi ((starRingEnd ℂ) s.ρ)
  shift2 :
    wp2At m s 2 = deriv (deriv Xi) ((starRingEnd ℂ) s.ρ)

/-- Single semantic assumption for the `p=3` prime window at order `m`. -/
class JetShiftExact_wp3At (m : ℕ) (s : Hyperlocal.OffSeed Xi) : Prop where
  shift0 :
    wp3At m s 0 = Xi (1 - (starRingEnd ℂ) s.ρ)
  shift1 :
    wp3At m s 1 = deriv Xi (1 - (starRingEnd ℂ) s.ρ)
  shift2 :
    wp3At m s 2 = deriv (deriv Xi) (1 - (starRingEnd ℂ) s.ρ)

/-- From the single semantic knob, get `IsJet3At` for `wp2At`. -/
theorem isJet3At_wp2At_of_shift
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) [JetShiftExact_wp2At m s] :
    IsJet3At Xi ((starRingEnd ℂ) s.ρ) (wp2At m s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa using (JetShiftExact_wp2At.shift0 (m := m) (s := s))
  · simpa using (JetShiftExact_wp2At.shift1 (m := m) (s := s))
  · simpa using (JetShiftExact_wp2At.shift2 (m := m) (s := s))

/-- From the single semantic knob, get `IsJet3At` for `wp3At`. -/
theorem isJet3At_wp3At_of_shift
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) [JetShiftExact_wp3At m s] :
    IsJet3At Xi (1 - (starRingEnd ℂ) s.ρ) (wp3At m s) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simpa using (JetShiftExact_wp3At.shift0 (m := m) (s := s))
  · simpa using (JetShiftExact_wp3At.shift1 (m := m) (s := s))
  · simpa using (JetShiftExact_wp3At.shift2 (m := m) (s := s))

end TAC

end XiPacket
end Targets
end Hyperlocal
