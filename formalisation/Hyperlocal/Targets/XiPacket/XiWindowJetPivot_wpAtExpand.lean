/-
  Hyperlocal/Targets/XiPacket/XiWindowJetPivot_wpAtExpand.lean

  Purely algebraic expansions for the prime windows `wpAt`, `wp2At`, `wp3At`.

  Goal:
  * make the affine structure explicit:
      wpAt = w0At + aCoeff⋅wc + bCoeff⋅ws
  * provide:
      - a pointwise simp lemma `wpAt_apply`
      - a `funext`/`Window` ext lemma `wpAt_ext`
      - three simp lemmas for indices 0/1/2 (useful for Jet3 goals)
  * cycle-safe: no Row0 semantics/extractor imports.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Complex
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

namespace JetPivot

/-- Pointwise expansion of `wpAt` (this is definitional, but nicer to rewrite with). -/
@[simp] theorem wpAt_apply (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) (i : Fin 3) :
    wpAt m s p i
      =
    (w0At m s) i
      + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s i))
      + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s i)) := by
  rfl

/-- Window ext lemma for `wpAt`: if the 3 coordinates match, the windows match. -/
theorem wpAt_ext
    (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ)
    (W : Transport.Window 3)
    (h0 : W 0 = (w0At m s) 0
            + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 0))
            + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 0)))
    (h1 : W 1 = (w0At m s) 1
            + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 1))
            + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 1)))
    (h2 : W 2 = (w0At m s) 2
            + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 2))
            + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 2))) :
    W = wpAt m s p := by
  funext i
  fin_cases i
  · simpa [wpAt_apply] using h0
  · simpa [wpAt_apply] using h1
  · simpa [wpAt_apply] using h2

/-- Index-0 expansion (useful for Jet3 goals). -/
@[simp] theorem wpAt_f0 (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    wpAt m s p 0
      =
    (w0At m s) 0
      + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 0))
      + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 0)) := by
  simp [wpAt_apply]

/-- Index-1 expansion (useful for Jet3 goals). -/
@[simp] theorem wpAt_f1 (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    wpAt m s p 1
      =
    (w0At m s) 1
      + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 1))
      + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 1)) := by
  simp [wpAt_apply]

/-- Index-2 expansion (useful for Jet3 goals). -/
@[simp] theorem wpAt_f2 (m : ℕ) (s : Hyperlocal.OffSeed Xi) (p : ℕ) :
    wpAt m s p 2
      =
    (w0At m s) 2
      + ((aCoeff (σ s) (t s) (p : ℝ) : ℂ) * (wc s 2))
      + ((bCoeff (σ s) (t s) (p : ℝ) : ℂ) * (ws s 2)) := by
  simp [wpAt_apply]

/-! ### Specialisations: `wp2At` and `wp3At` -/

@[simp] theorem wp2At_apply (m : ℕ) (s : Hyperlocal.OffSeed Xi) (i : Fin 3) :
    wp2At m s i
      =
    (w0At m s) i
      + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (wc s i))
      + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (ws s i)) := by
  -- wp2At is definitional wpAt with p=2
  rfl

@[simp] theorem wp3At_apply (m : ℕ) (s : Hyperlocal.OffSeed Xi) (i : Fin 3) :
    wp3At m s i
      =
    (w0At m s) i
      + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (wc s i))
      + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (ws s i)) := by
  rfl

@[simp] theorem wp2At_f0 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp2At m s 0
      =
    (w0At m s) 0
      + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (wc s 0))
      + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (ws s 0)) := by
  simp [wp2At_apply]

@[simp] theorem wp2At_f1 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp2At m s 1
      =
    (w0At m s) 1
      + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (wc s 1))
      + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (ws s 1)) := by
  simp [wp2At_apply]

@[simp] theorem wp2At_f2 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp2At m s 2
      =
    (w0At m s) 2
      + ((aCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (wc s 2))
      + ((bCoeff (σ s) (t s) (2 : ℝ) : ℂ) * (ws s 2)) := by
  simp [wp2At_apply]

@[simp] theorem wp3At_f0 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp3At m s 0
      =
    (w0At m s) 0
      + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (wc s 0))
      + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (ws s 0)) := by
  simp [wp3At_apply]

@[simp] theorem wp3At_f1 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp3At m s 1
      =
    (w0At m s) 1
      + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (wc s 1))
      + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (ws s 1)) := by
  simp [wp3At_apply]

@[simp] theorem wp3At_f2 (m : ℕ) (s : Hyperlocal.OffSeed Xi) :
    wp3At m s 2
      =
    (w0At m s) 2
      + ((aCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (wc s 2))
      + ((bCoeff (σ s) (t s) (3 : ℝ) : ℂ) * (ws s 2)) := by
  simp [wp3At_apply]

end JetPivot

end XiPacket
end Targets
end Hyperlocal
