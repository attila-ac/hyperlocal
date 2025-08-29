import Mathlib.Algebra.Polynomial.Basic   -- ✅ exists in your snapshot
import Hyperlocal.Core

noncomputable section
open Polynomial

namespace Hyperlocal.MinimalModel

/-- Linear factor `X - C z`. -/
def lin (z : ℂ) : Polynomial ℂ := X - C z

/-- Quartic with roots `{ρ, ⋆ρ, 1-ρ, 1-⋆ρ}`. -/
def quartetPoly (ρ : ℂ) : Polynomial ℂ :=
  lin ρ * lin (star ρ) * lin (Hyperlocal.oneMinus ρ) * lin (Hyperlocal.oneMinus (star ρ))

end Hyperlocal.MinimalModel
