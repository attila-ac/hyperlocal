/-
NEW FILE:
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_JetConvolutionAtFromRouteA.lean

Purpose:
  Provide the theorem-level API

    xiJetConvolutionAt_w0 / wc / wp2 / wp3

  that your “Next task” acceptance criterion asks for, in a single dedicated place,
  and re-exportable downstream.

Status:
  This *centralizes* the remaining Row--0 semantic gate in one file.
  The actual derivation “from Route--A factorisation + Cauchy-product recurrence lemma”
  is still the missing proof content (i.e. these are axioms for now), but:
    • `JetConvolutionAt` is no longer assumed ad hoc in consumer files;
    • everything downstream can now depend only on these theorem names.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_CauchySemantics
import Hyperlocal.Targets.XiPacket.XiAnalyticInputs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

namespace JetQuotOp

/-!
  # Row--0 semantic gate: `JetConvolutionAt` for the canonical ξ-windows

  The Row--0 bridge (`XiRow0Bridge_CauchySemantics.lean`) is purely algebraic once the
  single semantic predicate `JetConvolutionAt` is available for the canonical windows.

  This file is the unique home for discharging that semantic gate.

  At this stage we keep the analytic content isolated as axioms local to ξ.
  Downstream files should depend only on the theorem-level wrappers
  `xiJetConvolutionAt_*` provided below.
-/

/-!
### Semantic hypotheses (to be replaced by the recurrence extraction proof)

These are the only remaining analytic inputs needed for the Row--0 bridge.
They are phrased in the exact `JetConvolutionAt` form consumed by the Cauchy normal form.
-/

axiom Xi_jetConvolutionAt_w0  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (w0 s)

axiom Xi_jetConvolutionAt_wc  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wc s)

axiom Xi_jetConvolutionAt_wp2 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp2 s)

axiom Xi_jetConvolutionAt_wp3 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp3 s)

/-! ### Theorem-level API (consumed downstream) -/

theorem xiJetConvolutionAt_w0  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (w0 s) := by
  simpa using Xi_jetConvolutionAt_w0 (s := s)

theorem xiJetConvolutionAt_wc  (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wc s) := by
  simpa using Xi_jetConvolutionAt_wc (s := s)

theorem xiJetConvolutionAt_wp2 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp2 s) := by
  simpa using Xi_jetConvolutionAt_wp2 (s := s)

theorem xiJetConvolutionAt_wp3 (s : _root_.Hyperlocal.OffSeed Xi) :
  JetConvolutionAt s (rho s) (wp3 s) := by
  simpa using Xi_jetConvolutionAt_wp3 (s := s)

end JetQuotOp
end XiPacket
end Targets
end Hyperlocal
