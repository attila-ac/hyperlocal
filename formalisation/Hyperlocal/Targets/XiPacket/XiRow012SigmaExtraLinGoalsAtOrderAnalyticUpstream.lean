/-
  Hyperlocal/Targets/XiPacket/XiRow012SigmaExtraLinGoalsAtOrderAnalyticUpstream.lean

  Analytic-only target scaffold for FULL R0 (Path A, semantic form).

  DAG-clean refinement:
  * The three ExtraLin goals are derived purely algebraically from a coords01 provider
    (`XiAtOrderCoords01Out m s`) via `row012ExtraLin_of_coords`.
  * We do NOT import extractor-facing modules here.
  * Coords01 data is supplied via the typeclass `XiAtOrderCoords01Provider`, so we can
    swap instances (axiom / extractor glue / future true analytic proof) without changing
    this file.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_AtOrderCoords01Provider
import Hyperlocal.Targets.XiPacket.XiRow0Bridge_Row012ExtraLinToCoords
import Hyperlocal.Targets.XiPacket.XiRow012SigmaExtraLinGoalsAtOrderDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Hyperlocal.Transport
open Hyperlocal.Cancellation

/-!
## Named subgoals (the true analytic surface)

* row0Sigma = 0  for w0At/wp2At/wp3At
* coordinate vanishings (0/1) for w0At/wp2At/wp3At (packaged as `XiAtOrderCoords01Out`),
  supplied by a provider instance.

Everything downstream remains purely algebraic/bridges.
-/

abbrev SigmaGoal_w0At (m : ℕ) (s : OffSeed Xi) : Prop :=
  row0Sigma s (w0At m s) = 0

abbrev SigmaGoal_wp2At (m : ℕ) (s : OffSeed Xi) : Prop :=
  row0Sigma s (wp2At m s) = 0

abbrev SigmaGoal_wp3At (m : ℕ) (s : OffSeed Xi) : Prop :=
  row0Sigma s (wp3At m s) = 0

abbrev ExtraLinGoal_w0At (m : ℕ) (s : OffSeed Xi) : Prop :=
  Row012ExtraLin s (w0At m s)

abbrev ExtraLinGoal_wp2At (m : ℕ) (s : OffSeed Xi) : Prop :=
  Row012ExtraLin s (wp2At m s)

abbrev ExtraLinGoal_wp3At (m : ℕ) (s : OffSeed Xi) : Prop :=
  Row012ExtraLin s (wp3At m s)

/-!
## Temporary placeholders (replace one-by-one by real analytic proofs)

Only the three sigma facts remain axiomatized here.
Coords01 is supplied by the typeclass `XiAtOrderCoords01Provider`.
-/

axiom sigmaGoal_w0At_analytic
    (m : ℕ) (s : OffSeed Xi) : SigmaGoal_w0At m s

axiom sigmaGoal_wp2At_analytic
    (m : ℕ) (s : OffSeed Xi) : SigmaGoal_wp2At m s

axiom sigmaGoal_wp3At_analytic
    (m : ℕ) (s : OffSeed Xi) : SigmaGoal_wp3At m s

/-- Coords01 goal, obtained from the provider instance (DAG-clean). -/
theorem coords01Goal_analytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    XiAtOrderCoords01Out m s :=
  xiAtOrderCoords01Out_provided (m := m) (s := s)

/-!
## Derived ExtraLin goals (pure algebra from coords01)
-/

theorem extraLinGoal_w0At_analytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    ExtraLinGoal_w0At m s := by
  classical
  have HC : XiAtOrderCoords01Out m s := coords01Goal_analytic (m := m) (s := s)
  exact row012ExtraLin_of_coords (s := s) (w := w0At m s) HC.hw0At0 HC.hw0At1

theorem extraLinGoal_wp2At_analytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    ExtraLinGoal_wp2At m s := by
  classical
  have HC : XiAtOrderCoords01Out m s := coords01Goal_analytic (m := m) (s := s)
  exact row012ExtraLin_of_coords (s := s) (w := wp2At m s) HC.hwp2At0 HC.hwp2At1

theorem extraLinGoal_wp3At_analytic
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    ExtraLinGoal_wp3At m s := by
  classical
  have HC : XiAtOrderCoords01Out m s := coords01Goal_analytic (m := m) (s := s)
  exact row012ExtraLin_of_coords (s := s) (w := wp3At m s) HC.hwp3At0 HC.hwp3At1

/-!
## Final packaging theorem
-/

theorem xiRow012SigmaExtraLinGoalsAtOrder_analytic_upstream
    (m : ℕ) (s : OffSeed Xi) [XiAtOrderCoords01Provider] :
    XiRow012SigmaExtraLinGoalsAtOrder m s := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [SigmaGoal_w0At] using (sigmaGoal_w0At_analytic (m := m) (s := s))
  · simpa [ExtraLinGoal_w0At] using (extraLinGoal_w0At_analytic (m := m) (s := s))
  · simpa [SigmaGoal_wp2At] using (sigmaGoal_wp2At_analytic (m := m) (s := s))
  · simpa [ExtraLinGoal_wp2At] using (extraLinGoal_wp2At_analytic (m := m) (s := s))
  · simpa [SigmaGoal_wp3At] using (sigmaGoal_wp3At_analytic (m := m) (s := s))
  · simpa [ExtraLinGoal_wp3At] using (extraLinGoal_wp3At_analytic (m := m) (s := s))

end XiPacket
end Targets
end Hyperlocal
