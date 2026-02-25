/-
  Hyperlocal/Targets/XiPacket/TACTransportTruncated_AnalyticBridge.lean

  Hook layer between the finite Toeplitz transport matrix `T(δ)` and
  actual analytic derivative-shift identities.

  DESIGN:
  * Cycle-safe: no Row0 semantics/extractor imports.
  * Provides a purely finite lemma target expanding `transportMat.mulVec`.
  * Isolates the genuine analytic burden behind ONE predicate/class:
      `JetShiftExact`.

  IMPORTANT:
  * This file must compile with the project's Mathlib snapshot.
    (In particular, we do NOT import `Mathlib.Analysis.Calculus.Deriv.Iterated`
     because it is not present in your snapshot.)
-/

import Hyperlocal.Targets.XiPacket.TACTransportTruncated
import Hyperlocal.Targets.XiPacket.TACTransportTruncated_RangeReindex
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped BigOperators

namespace TAC

/-- Convenience: iterated complex derivative operator. -/
def cderivIter (m : ℕ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (deriv^[m] f)

/-- The length-`N` jet vector of raw derivatives at `z`: `Γ j = f^(j)(z)`. -/
def jetVec (N : ℕ) (f : ℂ → ℂ) (z : ℂ) : Fin N → ℂ :=
  fun j => cderivIter (j : ℕ) f z

/--
Purely finite expansion lemma (algebraic target):

`transport N δ (jetVec N f z) j` is the truncated Taylor-shift stencil

`∑_{r=0}^{N-1-j} f^(j+r)(z) * δ^r / r!`.

This lemma is *pure algebra* about `transportMat` and `mulVec`.
-/
theorem transport_apply_eq_truncSum
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) (j : Fin N) :
    transport N δ (jetVec N f z) j
      =
    (Finset.range (N - (j : ℕ))).sum (fun r =>
      (cderivIter ((j : ℕ) + r) f z) * (δ ^ r) / (Nat.factorial r : ℂ)) := by
  classical
  -- Start from the snapshot-robust finitary endpoint proved in
  -- `TACTransportTruncated_RangeReindex.lean`.
  have h :=
    (transport_apply_eq_truncSum_finite_attach
      (N := N) (Γ := jetVec N f z) (δ := δ) (j := j))

  -- Simplify the summand to an expression only in terms of `r.1 : ℕ`.
  have h' :
      transport N δ (jetVec N f z) j
        =
      ((Finset.range (N - (j : ℕ))).attach).sum (fun r =>
        (cderivIter ((j : ℕ) + r.1) f z) * (δ ^ r.1) / (Nat.factorial r.1 : ℂ)) := by
    -- In `transport_apply_eq_truncSum_finite_attach`, the factor is
    -- `((δ^r)/r!) * Γ (j+r)`. Here `Γ = jetVec`, so `Γ (j+r) = cderivIter (j+r) f z`.
    -- We also commute the multiplication to match the preferred order.
    simpa [jetVec, cderivIter, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h

  -- Eliminate `.attach` by a bijection `r ↦ r.1`.
  have hsum :
      ((Finset.range (N - (j : ℕ))).attach).sum (fun r =>
          (cderivIter ((j : ℕ) + r.1) f z) * (δ ^ r.1) / (Nat.factorial r.1 : ℂ))
        =
      (Finset.range (N - (j : ℕ))).sum (fun r =>
          (cderivIter ((j : ℕ) + r) f z) * (δ ^ r) / (Nat.factorial r : ℂ)) := by
    let s : Finset { r // r ∈ Finset.range (N - (j : ℕ)) } :=
      (Finset.range (N - (j : ℕ))).attach
    let t : Finset ℕ := Finset.range (N - (j : ℕ))
    refine Finset.sum_bij
      (s := s) (t := t)
      (i := fun r _ => r.1)
      (f := fun r => (cderivIter ((j : ℕ) + r.1) f z) * (δ ^ r.1) /
        (Nat.factorial r.1 : ℂ))
      (g := fun r => (cderivIter ((j : ℕ) + r) f z) * (δ ^ r) /
        (Nat.factorial r : ℂ))
      ?_ ?_ ?_ ?_
    · intro r hr
      -- membership of `r.1` in the underlying range is exactly `r.2`.
      simpa [s, t] using r.2
    · intro r₁ hr₁ r₂ hr₂ hEq
      apply Subtype.ext
      exact hEq
    · intro r hr
      refine ⟨⟨r, hr⟩, ?_, rfl⟩
      simp [s]
    · intro r hr
      rfl

  -- Finish.
  simpa [h'] using (h'.trans hsum)

/-
  === The real analytic bridge you need (future discharge site) ===

  Your transport operator is *truncated*. Exact analytic translation is infinite,
  but becomes exact in a truncated jet/quotient model.

  We isolate that missing analytic “exactness in quotient” behind one class.
-/

/--
Bridge predicate (draft):

`JetShiftExact N f z δ` is meant to assert that the truncated transport is
the correct jet-transport for `f` at `z` with shift `δ` in your chosen jet/quotient model.

Right now it is intentionally minimal so downstream code can depend on it
without forcing the final analytic formalisation.
-/
class JetShiftExact (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) : Prop :=
  (shift_ok : True)

/-- Minimal hook lemma: everything downstream should depend on THIS, not on ad-hoc axioms. -/
theorem jet_shift_hook
    (N : ℕ) (f : ℂ → ℂ) (z δ : ℂ) [JetShiftExact N f z δ] :
    True := by
  exact (JetShiftExact.shift_ok (N := N) (f := f) (z := z) (δ := δ))

end TAC

end XiPacket
end Targets
end Hyperlocal
