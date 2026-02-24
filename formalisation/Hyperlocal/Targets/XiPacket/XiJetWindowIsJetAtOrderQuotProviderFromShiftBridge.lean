/-
  Hyperlocal/Targets/XiPacket/XiJetWindowIsJetAtOrderQuotProviderFromShiftBridge.lean

  Q1 plumbing (quotient arm, cycle-safe):

  Package the ShiftBridge interface

      [JetQuotShiftBridge3AtOrderQuot m s z w]

  into a small provider that yields the desired jet facts for the concrete windows
  w0At/wp2At/wp3At at the Route-A quotient anchors, *assuming* the JetQuot recurrence
  holds on padSeq3 of the window.

  IMPORTANT:
  This file does NOT assume the ShiftBridge instances are globally available.
  Instead, each method takes the needed ShiftBridge instance as an implicit argument
  at the point of use (so the file compiles even before those instances exist).
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_JetQuotShiftBridgeAtOrderQuot
import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
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
Provider form of “Q1 jet facts” (quotient arm):

Gives `IsJet3AtOrderQuot` for the three concrete windows at the intended anchors,
*assuming* you have the JetQuot recurrence proof on `padSeq3` of each window.

Crucially: the required `JetQuotShiftBridge3AtOrderQuot ...` instance is required
*at use time* (as an implicit argument to each method), not globally.
-/
class XiJetWindowIsJetAtOrderQuotProvider : Prop where
  /-- w0At is a quotient 3-jet at anchor `s.ρ`, assuming recurrence on `padSeq3 (w0At m s)`. -/
  w0At_isJet3AtOrderQuot :
      ∀ (m : ℕ) (s : OffSeed Xi),
        [JetQuotShiftBridge3AtOrderQuot m s (s.ρ) (w0At m s)] →
        JetQuotRec2 s (padSeq3 (w0At m s)) →
          IsJet3AtOrderQuot m s (s.ρ) (w0At m s)

  /-- wp2At is a quotient 3-jet at anchor `conj(s.ρ)`, assuming recurrence on `padSeq3 (wp2At m s)`. -/
  wp2At_isJet3AtOrderQuot :
      ∀ (m : ℕ) (s : OffSeed Xi),
        [JetQuotShiftBridge3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)] →
        JetQuotRec2 s (padSeq3 (wp2At m s)) →
          IsJet3AtOrderQuot m s ((starRingEnd ℂ) s.ρ) (wp2At m s)

  /-- wp3At is a quotient 3-jet at anchor `1 - conj(s.ρ)`, assuming recurrence on `padSeq3 (wp3At m s)`. -/
  wp3At_isJet3AtOrderQuot :
      ∀ (m : ℕ) (s : OffSeed Xi),
        [JetQuotShiftBridge3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)] →
        JetQuotRec2 s (padSeq3 (wp3At m s)) →
          IsJet3AtOrderQuot m s (1 - (starRingEnd ℂ) s.ρ) (wp3At m s)

/--
Canonical construction: the provider is just “apply the bridge lemma”.

This compiles immediately because it does NOT try to synthesize any bridge instances
until the methods are actually used.
-/
instance instXiJetWindowIsJetAtOrderQuotProviderFromShiftBridge :
    XiJetWindowIsJetAtOrderQuotProvider := by
  refine ⟨?_, ?_, ?_⟩
  · intro m s _Hbridge Hrec
    exact isJet3AtOrderQuot_w0At_of_rec2 (m := m) (s := s) (z := s.ρ) Hrec
  · intro m s _Hbridge Hrec
    exact isJet3AtOrderQuot_wp2At_of_rec2
      (m := m) (s := s) (z := (starRingEnd ℂ) s.ρ) Hrec
  · intro m s _Hbridge Hrec
    exact isJet3AtOrderQuot_wp3At_of_rec2
      (m := m) (s := s) (z := 1 - (starRingEnd ℂ) s.ρ) Hrec

end TAC

end XiPacket
end Targets
end Hyperlocal
