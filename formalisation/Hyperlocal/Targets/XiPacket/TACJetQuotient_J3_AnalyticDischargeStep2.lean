/-
  Hyperlocal/Targets/XiPacket/TACJetQuotient_J3_AnalyticDischargeStep2.lean

  Step 2b (analytic discharge):

  Use Mathlib Taylor for entire functions to identify the J3 jet coefficients:
    coeff0 = f(c+δ)
    coeff1 = f'(c+δ)
    coeff2 = f''(c+δ)

  and therefore:
    taylorJet2J3 f c δ = J3Jet2 f (c+δ).

  This is the "real analytic discharge" statement in quotient semantics.
-/

import Hyperlocal.Targets.XiPacket.TACJetQuotient_J3_TaylorEval
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket
namespace TAC
namespace J3

open Complex
open scoped BigOperators

/--
Analytic discharge, packaged as the three coefficient identifications.
These are the facts you’ll feed into your transport/Toeplitz match later.
-/
theorem coeff012_of_entire'
    (f : ℂ → ℂ)
    (hf0 : Differentiable ℂ f)
    (hf1 : Differentiable ℂ (fun z => deriv f z))
    (hf2 : Differentiable ℂ (fun z => deriv (deriv f) z))
    (c δ : ℂ) :
    coeff0 f c δ = f (c + δ)
      ∧ coeff1 f c δ = deriv f (c + δ)
      ∧ coeff2 f c δ = deriv (deriv f) (c + δ) := by
  refine ⟨?_, ?_, ?_⟩
  · exact coeff0_eq_of_entire' (f := f) hf0 (c := c) (δ := δ)
  · exact coeff1_eq_of_entire' (f := f) hf1 (c := c) (δ := δ)
  · exact coeff2_eq_of_entire' (f := f) hf2 (c := c) (δ := δ)

/--
The canonical Step-2 discharge statement:
the J3-truncated germ (Taylor-evaluate then truncate in w) equals the canonical jet at c+δ.
-/
theorem taylorJet2J3_eq_J3Jet2_of_entire'_step2
    (f : ℂ → ℂ)
    (hf0 : Differentiable ℂ f)
    (hf1 : Differentiable ℂ (fun z => deriv f z))
    (hf2 : Differentiable ℂ (fun z => deriv (deriv f) z))
    (c δ : ℂ) :
    taylorJet2J3 f c δ = J3Jet2 f (c + δ) :=
  taylorJet2J3_eq_J3Jet2_of_entire' (f := f) hf0 hf1 hf2 (c := c) (δ := δ)

end J3
end TAC
end XiPacket
end Targets
end Hyperlocal
