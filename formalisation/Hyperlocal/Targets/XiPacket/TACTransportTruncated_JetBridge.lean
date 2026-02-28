/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_JetBridge.lean

  Step 3 (finitary): Jet-facing bridge lemmas for the truncated transport stencil.

  We provide BOTH normal forms:

  (1) filtered-sum form:
        ∑ m in univ.filter (j ≤ m), ...

  (2) canonical range/attach form (preferred):
        ∑ r in (range (N - j)).attach, ... at index (j + r.1)

  Task C goal is to make (2) available so landing files never need to mention filter sums.
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated_Finite
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_RangeReindex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC

open scoped BigOperators

/-- iterated complex derivative -/
def cderivIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (deriv^[m] f)

/-- jet vector -/
def jetVec (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : Fin N → ℂ :=
  fun j => cderivIter (j : ℕ) f z

/--
Jet version of the finite transport expansion.

This is still the “truncated Taylor stencil”, presented as a filtered sum.
-/
theorem transport_apply_eq_filterSum_jet
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) (j : Fin N) :
    transport N δ (jetVec N f z) j
      =
    ((Finset.univ.filter (fun m : Fin N => j ≤ m)).sum (fun m : Fin N =>
        (δ ^ ((m : ℕ) - (j : ℕ))) /
            (Nat.factorial ((m : ℕ) - (j : ℕ)) : ℂ)
          * cderivIter (m : ℕ) f z)) := by
  classical
  simpa [jetVec] using
    (transport_apply_eq_filterSum (N := N) (Γ := jetVec N f z) (δ := δ) (j := j))

/--
Preferred normal form (Task C):

Specialize the canonical attached-range truncation sum to the jet vector.
This removes all `univ.filter (j ≤ m)` friction from downstream landing files.
-/
theorem transport_apply_eq_range_attachSum_jet
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) (j : Fin N) :
    transport N δ (jetVec N f z) j
      =
    ((Finset.range (N - (j : ℕ))).attach).sum (fun r =>
      ((δ ^ r.1) / (Nat.factorial r.1 : ℂ))
        * cderivIter ((j : ℕ) + r.1) f z) := by
  classical
  -- Reuse the Step-3 endpoint already proved in `TACTransportTruncated_RangeReindex`.
  -- It gives the attached-range sum with a generic Γ; we specialize Γ := jetVec.
  simpa [jetVec] using
    (transport_apply_eq_truncSum_finite_attach
      (N := N) (Γ := jetVec N f z) (δ := δ) (j := j))

/--
Optional: eliminate `.attach` and use `Fin (N - j)` as the canonical index type,
again specialized to the jet vector.
-/
theorem transport_apply_eq_range_finSum_jet
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) (j : Fin N) :
    transport N δ (jetVec N f z) j
      =
    (Finset.univ : Finset (Fin (N - (j : ℕ)))).sum (fun r =>
      ((δ ^ (r : ℕ)) / (Nat.factorial (r : ℕ) : ℂ))
        * cderivIter ((j : ℕ) + (r : ℕ)) f z) := by
  classical
  simpa [jetVec] using
    (transport_apply_eq_truncSum_finite_fin
      (N := N) (Γ := jetVec N f z) (δ := δ) (j := j))

end TAC
end XiPacket
end Targets
end Hyperlocal
