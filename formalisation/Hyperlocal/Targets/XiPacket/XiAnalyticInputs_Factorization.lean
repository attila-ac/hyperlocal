import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Polynomial.Basic

import Hyperlocal.Targets.RiemannXi
import Hyperlocal.Core
import Hyperlocal.Factorization
import Hyperlocal.FactorizationRC
import Hyperlocal.MinimalModel
import Hyperlocal.FactorizationGofSEntire
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Hyperlocal.GrowthOrder

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open Polynomial
open Hyperlocal.MinimalModel
open Hyperlocal.Factorization

/-!
  Factorisation handoff (Route A):
  keep this axiom isolated until you later replace it by Mathlib-level structure.
-/

/-- Route-A handoff: existence of an entire quotient after factoring out the quartet. -/
axiom Xi_exists_factorisedByQuartet_entire (s : OffSeed Xi) :
  ∃ G : ℂ → ℂ, FactorisedByQuartet Xi s.ρ 1 G ∧ GrowthOrder.EntireFun G

/-- The explicit FE/RC quartet polynomial (order 1). -/
def Rquartet (ρ : ℂ) : Polynomial ℂ :=
  (X - C ρ) * (X - C (star ρ)) * (X - C (1 - ρ)) * (X - C (1 - star ρ))

lemma Rquartet_eval_rho (ρ : ℂ) : (Rquartet ρ).eval ρ = 0 := by simp [Rquartet]
lemma Rquartet_eval_star (ρ : ℂ) : (Rquartet ρ).eval (star ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus (ρ : ℂ) : (Rquartet ρ).eval (1 - ρ) = 0 := by simp [Rquartet]
lemma Rquartet_eval_oneMinus_star (ρ : ℂ) : (Rquartet ρ).eval (1 - star ρ) = 0 := by simp [Rquartet]

lemma R_quartet_zeros (s : OffSeed Xi) :
    (Rquartet s.ρ).eval s.ρ = 0 ∧
    (Rquartet s.ρ).eval (star s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - s.ρ) = 0 ∧
    (Rquartet s.ρ).eval (1 - star s.ρ) = 0 := by
  refine And.intro (Rquartet_eval_rho s.ρ) ?_
  refine And.intro (Rquartet_eval_star s.ρ) ?_
  refine And.intro (Rquartet_eval_oneMinus s.ρ) ?_
  exact Rquartet_eval_oneMinus_star s.ρ

/-- Packaged handoff. -/
theorem G_Xi_entire (s : OffSeed Xi) :
    ∃ G : ℂ → ℂ, FactorisedByQuartet Xi s.ρ 1 G ∧ GrowthOrder.EntireFun G := by
  exact Xi_exists_factorisedByQuartet_entire s

end XiPacket
end Targets
end Hyperlocal
