/-
  Hyperlocal/FactorizationConsequences.lean

  Thin wrappers collecting direct consequences of the factorisation
  H = R_{rho,k} · G for the upstream→downstream handoff:
  (i) order ≤ 1 passes forward to H;
  (ii) transcendence passes back to G.
-/

import Mathlib.Data.Complex.Basic
import Hyperlocal.Factorization
import Hyperlocal.GrowthOrder
import Hyperlocal.Transcendence

noncomputable section
open scoped Classical

namespace Hyperlocal
namespace Consequences

/-- Growth forward: if `G` has order ≤ 1, then so does
    `H(s) = (R_{rho,k} rho k).eval s * G s`. -/
lemma orderLEOne_for_H_of_orderLEOne_for_G
    {G : ℂ → ℂ} (rho : ℂ) (k : ℕ) (hG : Hyperlocal.GrowthOrder.OrderLEOne G) :
    Hyperlocal.GrowthOrder.OrderLEOne
      (fun s => (Hyperlocal.Factorization.Rρk rho k).eval s * G s) := by
  -- unpack the Prop-level witnesses for G
  rcases hG with ⟨A, B, hA, hB, hbound⟩
  -- repackage as a bundled Order1Bound and use the existing finisher
  let hG_bundled : Hyperlocal.GrowthOrder.Order1Bound G := ⟨A, B, hA, hB, hbound⟩
  exact (Hyperlocal.GrowthOrder.order1_for_H_of_order1_for_G rho k hG_bundled).to_OrderLEOne

/-- Transcendence back: if `H = (R_{rho,k}).eval * G` and `H` is transcendental,
    then `G` is transcendental (uses that `R_{rho,k}` is a polynomial). -/
lemma G_transcendental_of_RrhoK_factor
    {H G : ℂ → ℂ} (rho : ℂ) (k : ℕ)
    (hH : Hyperlocal.Transcendence.Transcendental H)
    (hfac : ∀ z, H z = ((Hyperlocal.Factorization.Rρk rho k).eval z) * G z) :
    Hyperlocal.Transcendence.Transcendental G :=
  Hyperlocal.Transcendence.G_transcendental_of_eval_poly_factor
    (Hyperlocal.Factorization.Rρk rho k) hH hfac

end Consequences
end Hyperlocal
