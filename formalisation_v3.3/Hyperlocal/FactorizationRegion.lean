import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Mathlib.Data.Set.Basic

namespace Hyperlocal
namespace FactorizationRegion

open Set

/-- “Zero-free on U” for the quartet factor. We require nonvanishing both at `s`
    and at `star s` to keep the wrapper independent from algebraic RC of `R`. -/
def ZeroFreeOn (ρ : ℂ) (k : ℕ) (U : Set ℂ) : Prop :=
  (∀ ⦃s⦄, s ∈ U → (Factorization.Rρk ρ k).eval s ≠ 0) ∧
  (∀ ⦃s⦄, s ∈ U → (Factorization.Rρk ρ k).eval (star s) ≠ 0)

/-- On a zero-free region `U`, `G` inherits both FE and RC pointwise on `U`. -/
lemma G_satisfies_FE_RC_on
    {H G : ℂ → ℂ} {ρ : ℂ} {k : ℕ} {U : Set ℂ}
    (hfac : Factorization.FactorisedByQuartet H ρ k G)
    (HFE  : Factorization.FunFE H)
    (RFE  : Factorization.FE_R ρ k)
    (HRC  : FactorizationRC.FunRC H)
    (RRC  : FactorizationRC.RC_R ρ k)
    (hz   : ZeroFreeOn ρ k U) :
    ∀ ⦃s : ℂ⦄, s ∈ U →
      (G (Hyperlocal.oneMinus s) = G s) ∧ (G (star s) = star (G s)) := by
  intro s hs
  refine And.intro ?fe ?rc
  · -- FE on U
    have h_R_nonzero_s := hz.1 hs
    -- We use .symm to flip the equality from `G s = G (1-s)` to `G (1-s) = G s`.
    exact (Hyperlocal.Factorization.G_inherits_FE_off_zeros hfac HFE RFE h_R_nonzero_s).symm
  · -- RC on U
    have h_R_nonzero_star_s := hz.2 hs
    exact Hyperlocal.FactorizationRC.G_inherits_RC_off_zeros hfac HRC RRC h_R_nonzero_star_s

end FactorizationRegion
end Hyperlocal
