/-
  Hyperlocal/Targets/XiPacket/XiLocalFactor.lean

  Isolated “local analytic factor” lemma:

    xi a = 0  ⟹  ∃ J analytic at a,  xi z = (z - a) * J z

  In your snapshot you currently don't have a stable lemma name wired
  (your error shows `Hyperlocal.Removable.removable_div_sub_of_eq_zero` doesn't exist).

  Keep exactly ONE placeholder here until you locate/prove the theorem-level statement.
-/

import Hyperlocal.Targets.XiPacket.XiAnalyticInputs

import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex

/--
LOCAL FACTOR (isolated).

TODO: replace this axiom with the theorem-level lemma once located/proved:
- either from `Hyperlocal.Removable` (preferred), or
- from a Mathlib `AnalyticAt` power series factorization lemma.

Nothing else in the factorisation pipeline should depend on the lemma name.
-/
axiom xi_localFactor (a : ℂ) (ha : xi a = 0) :
    ∃ J : ℂ → ℂ, AnalyticAt ℂ J a ∧ (∀ z : ℂ, xi z = (z - a) * J z)

end XiPacket
end Targets
end Hyperlocal
