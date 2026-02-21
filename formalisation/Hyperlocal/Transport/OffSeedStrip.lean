/-
  Hyperlocal/Transport/OffSeedStrip.lean

  Seed refinement: off-seed constrained to the **critical strip**.

  This is used to discharge nondegeneracy facts (e.g. `σ3 ≠ 0`) from explicit
  inequalities on `Re(ρ)` together with the existing `Im(ρ) ≠ 0` hypothesis.

  IMPORTANT:
    This file is intentionally tiny and depends only on the core `OffSeed` record.
-/

import Hyperlocal.AdAbsurdumSetup
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal

/-- Off-seed with explicit critical-strip bounds `0 < Re(ρ) < 1`. -/
structure OffSeedStrip (H : ℂ → ℂ) extends OffSeed H where
  hRe_pos : 0 < ρ.re
  hRe_lt_one : ρ.re < 1

attribute [simp] OffSeedStrip.toOffSeed

instance {H : ℂ → ℂ} : Coe (OffSeedStrip H) (OffSeed H) where
  coe s := s.toOffSeed

@[simp] lemma OffSeedStrip_coe_rho {H : ℂ → ℂ} (s : OffSeedStrip H) : (s : OffSeed H).ρ = s.ρ := rfl
@[simp] lemma OffSeedStrip_coe_hρ {H : ℂ → ℂ} (s : OffSeedStrip H) : (s : OffSeed H).hρ = s.hρ := rfl
@[simp] lemma OffSeedStrip_coe_hσ {H : ℂ → ℂ} (s : OffSeedStrip H) : (s : OffSeed H).hσ = s.hσ := rfl
@[simp] lemma OffSeedStrip_coe_ht {H : ℂ → ℂ} (s : OffSeedStrip H) : (s : OffSeed H).ht = s.ht := rfl

end Hyperlocal
