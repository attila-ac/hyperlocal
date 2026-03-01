/-
  Hyperlocal/Targets/XiPacket/TACAnalytic_CDerivIterBridge.lean

  Tiny bridge lemma:
  project-level `cderivIter m f := deriv^[m] f` agrees with Mathlib's
  `iteratedDeriv m f`.

  This is the adapter needed to reuse lemmas stated in terms of `iteratedDeriv`
  when downstream goals are phrased with `cderivIter`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

namespace TAC

lemma cderivIter_eq_iteratedDeriv (m : ℕ) (f : ℂ → ℂ) :
    cderivIter m f = iteratedDeriv m f := by
  funext z
  -- `cderivIter` is `deriv^[m]`; Mathlib: `iteratedDeriv_eq_iterate`.
  -- Avoid simp loops: do a pointwise rewrite via congrArg.
  simpa [XiPacket.cderivIter] using
    (congrArg (fun g : ℂ → ℂ => g z)
      (iteratedDeriv_eq_iterate (n := m) (f := f))).symm

lemma cderivIter_apply (m : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    cderivIter m f z = iteratedDeriv m f z := by
  simpa using congrArg (fun g : ℂ → ℂ => g z) (cderivIter_eq_iteratedDeriv (m := m) (f := f))

end TAC

end XiPacket
end Targets
end Hyperlocal
