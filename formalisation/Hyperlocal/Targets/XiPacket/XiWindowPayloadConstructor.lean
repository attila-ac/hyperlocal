/-
  Hyperlocal/Targets/XiPacket/XiWindowPayloadConstructor.lean

  FULL REPLACEMENT (Option A compatibility).

  Fix:
    WindowPayload.hkappa is now an Or-shape, so constructors must supply:
      Or.inl hKap    (when given the real-block κ fact)
  No new axioms; purely adapts constructors to the widened payload field.
-/

import Hyperlocal.AdAbsurdumSetup
import Hyperlocal.Transport.PrimeTrigPacket
import Hyperlocal.Targets.XiPacket.Vectorize
import Hyperlocal.Targets.XiPacket.WindowPayload
import Hyperlocal.Targets.XiPacket.XiWindowDefs
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open scoped Real
open Hyperlocal.Transport
open Hyperlocal.Transport.PrimeTrigPacket

/-- Generic Phase-4 constructor: build `WindowPayload σ t` from B/C facts about five windows. -/
def windowPayload_mk_of_BC
    {σ t : ℝ}
    (W0 Wc Ws Wp2 Wp3 : Transport.Window 3)

    -- Lemma B (Trig split) at p=2,3
    (hW2 :
      ∀ i : Fin 3,
        Wp2 i = W0 i
          + ((aCoeff σ t (2 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff σ t (2 : ℝ) : ℂ) * (Ws i)))
    (hW3 :
      ∀ i : Fin 3,
        Wp3 i = W0 i
          + ((aCoeff σ t (3 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff σ t (3 : ℝ) : ℂ) * (Ws i)))

    -- Lemma C (ell/kappa consequences)
    (hEll2 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp2) = 0)
    (hEll3 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp3) = 0)
    (hKap  : Transport.kappa (reVec3 W0) (reVec3 Wc) (reVec3 Ws) ≠ 0)
    :
    WindowPayload σ t := by
  refine
    { w0 := W0
      wc := Wc
      ws := Ws
      wp2 := Wp2
      wp3 := Wp3
      hw2 := hW2
      hw3 := hW3
      hell2 := hEll2
      hell3 := hEll3
      hkappa := Or.inl hKap }

/--
Same constructor packaged for off-seeds:
build `WindowPayload s.ρ.re s.ρ.im` once you instantiate windows + B/C facts.
-/
def windowPayload_mk_of_BC_offSeed
    {H : ℂ → ℂ} (s : Hyperlocal.OffSeed H)
    (W0 Wc Ws Wp2 Wp3 : Transport.Window 3)

    -- Lemma B (Trig split) at p=2,3 using σ=s.ρ.re and t=s.ρ.im
    (hW2 :
      ∀ i : Fin 3,
        Wp2 i = W0 i
          + ((aCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * (Ws i)))
    (hW3 :
      ∀ i : Fin 3,
        Wp3 i = W0 i
          + ((aCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * (Wc i))
          + ((bCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * (Ws i)))

    -- Lemma C (ell/kappa consequences)
    (hEll2 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp2) = 0)
    (hEll3 : Transport.ell (reVec3 W0) (reVec3 Wc) (reVec3 Wp3) = 0)
    (hKap  : Transport.kappa (reVec3 W0) (reVec3 Wc) (reVec3 Ws) ≠ 0)
    :
    WindowPayload s.ρ.re s.ρ.im := by
  simpa using
    (windowPayload_mk_of_BC (σ := s.ρ.re) (t := s.ρ.im)
      W0 Wc Ws Wp2 Wp3 hW2 hW3 hEll2 hEll3 hKap)

/-!
## Xi-specialized Phase-4 constructor (Plan C++)

For ξ, the five windows are definitional from `XiWindowDefs.lean`:
  w0  wc  ws  wp2  wp3

and `wp2/wp3` are definitional trig-split linear combos of `w0/wc/ws`,
so Lemma-B obligations are discharged by `rfl`.

With Option A, `hkappa` is Or-shaped; we accept the real κ-fact and inject with `Or.inl`.
-/

/-- Definitional trig-split at p=2 for the ξ windows from `XiWindowDefs`. -/
@[simp] lemma xi_hW2 (s : Hyperlocal.OffSeed Xi) :
    ∀ i : Fin 3,
      (wp2 s) i = (w0 s) i
        + ((aCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * ((wc s) i))
        + ((bCoeff s.ρ.re s.ρ.im (2 : ℝ) : ℂ) * ((ws s) i)) := by
  intro i
  rfl

/-- Definitional trig-split at p=3 for the ξ windows from `XiWindowDefs`. -/
@[simp] lemma xi_hW3 (s : Hyperlocal.OffSeed Xi) :
    ∀ i : Fin 3,
      (wp3 s) i = (w0 s) i
        + ((aCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * ((wc s) i))
        + ((bCoeff s.ρ.re s.ρ.im (3 : ℝ) : ℂ) * ((ws s) i)) := by
  intro i
  rfl

/--
Plan C++ “tiny constructor” for ξ:

Build `WindowPayload s.ρ.re s.ρ.im` from Lemma C facts,
injecting the real-κ fact into the widened `hkappa` field.
-/
def xiWindowPayload_of_C
    (s : Hyperlocal.OffSeed Xi)
    (hEll2 : Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp2 s)) = 0)
    (hEll3 : Transport.ell (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (wp3 s)) = 0)
    (hKap  : Transport.kappa (reVec3 (w0 s)) (reVec3 (wc s)) (reVec3 (ws s)) ≠ 0)
    : WindowPayload s.ρ.re s.ρ.im := by
  -- Use the generic off-seed constructor then inject κ via Or.inl at the bottom layer.
  simpa using
    (windowPayload_mk_of_BC_offSeed (H := Xi) s
      (w0 s) (wc s) (ws s) (wp2 s) (wp3 s)
      (xi_hW2 (s := s)) (xi_hW3 (s := s))
      hEll2 hEll3 hKap)

end XiPacket
end Targets
end Hyperlocal
