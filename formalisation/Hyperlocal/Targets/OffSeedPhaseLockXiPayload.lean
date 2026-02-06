/-
  Hyperlocal/Targets/OffSeedPhaseLockXiPayload.lean

  Plan C++ endgame wrapper for the concrete target Xi := Hyperlocal.xi.

  IMPORTANT:
  - All plumbing is now green and semantic-free.
  - The *only* remaining ξ-semantic assumption lives in exactly one place:
        Targets/XiPacket/XiLemmaC_Semantic_FromRecurrence.lean

  This file merely composes:
    XiLemmaC_Semantic_fromRecurrence
      -> xiWindowPayload_of_semantic
      -> WindowPayload.toPrimeTrigPacket
      -> PrimeTrigPacket.offSeedPhaseLock_of_packet
-/

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Targets.XiPacket.XiLemmaC_Semantic_FromRecurrence
import Hyperlocal.Targets.XiPacket.XiLemmaC_SemanticToWindowPayload
import Hyperlocal.Targets.XiPacket.ToPrimeTrigPacket
import Hyperlocal.Transport.OffSeedBridge
import Hyperlocal.Transport.PrimeTrigPacket
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace Hyperlocal.Targets.OffSeedPhaseLockXiPayload

open scoped Real

/-- Notation: our concrete target Xi. -/
abbrev Xi : ℂ → ℂ := Hyperlocal.xi

/-- Payload constructor (now pure conversion from the single semantic cliff lemma). -/
def xiWindowPayload_of_window (s : Hyperlocal.OffSeed Xi) :
    Hyperlocal.Targets.XiPacket.WindowPayload
      (Hyperlocal.Targets.XiPacket.σ s) (Hyperlocal.Targets.XiPacket.t s) := by
  exact
    Hyperlocal.Targets.XiPacket.xiWindowPayload_of_semantic (s := s)
      (Hyperlocal.Targets.XiPacket.xiLemmaC_Semantic_fromRecurrence (s := s))

/-- Prime trig packet extracted from the payload (pure conversion). -/
def xiPrimeTrigPacket (s : Hyperlocal.OffSeed Xi) :
    Hyperlocal.Transport.PrimeTrigPacket.Packet
      (Hyperlocal.Targets.XiPacket.σ s) (Hyperlocal.Targets.XiPacket.t s) :=
  (xiWindowPayload_of_window s).toPrimeTrigPacket

/-- Off-seed phase-lock for Xi, derived from the trig packet. -/
theorem offSeedPhaseLock_Xi : Hyperlocal.Transport.OffSeedPhaseLock Xi := by
  intro s
  -- Packet -> (∃κ≠0, sin(t log2)=0 ∧ sin(t log3)=0), with t = Im(s.ρ).
  simpa [xiPrimeTrigPacket] using
    Hyperlocal.Transport.PrimeTrigPacket.offSeedPhaseLock_of_packet
      (xiPrimeTrigPacket s)

end Hyperlocal.Targets.OffSeedPhaseLockXiPayload
