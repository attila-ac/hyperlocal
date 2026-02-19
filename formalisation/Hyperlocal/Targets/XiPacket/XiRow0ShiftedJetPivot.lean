/-
  Hyperlocal/Targets/XiPacket/XiRow0ShiftedJetPivot.lean

  Definition of the shifted jet for the jet-pivot technique.

  NOTE (fix):
  * `XiTransportConvolution` is **not** under `Targets/XiPacket/`.
    The correct module name is `Hyperlocal.Targets.XiTransportConvolution`.
  * Avoid `vector` / `Ξ(k)(sc)` etc. The project already defines the order-m jet
    via `cderivIter` and `xiCentralJetAt` in `XiWindowJetPivotDefs.lean`.
-/

import Hyperlocal.Targets.XiPacket.XiWindowJetPivotDefs
import Hyperlocal.Targets.XiTransportConvolution
import Mathlib.Data.Complex.Basic

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped Real
open Hyperlocal.Transport

/-- Shifted (order-`k`) central jet at the anchor `sc s`.
This is just the existing `xiCentralJetAt k s`, re-exported under a “shifted jet” name. -/
def xiShiftedJetAt (k : ℕ) (s : OffSeed Xi) : Transport.Window 3 :=
  xiCentralJetAt k s

/-- Shifted transported window corresponding to the shifted jet.
This is just the existing `w0At k s`, re-exported under a “shifted window” name. -/
def xiShiftedWindow (k : ℕ) (s : OffSeed Xi) : Transport.Window 3 :=
  w0At k s

/-- A simple scalar diagnostic attached to the shifted jet: real part of the leading jet entry. -/
def xiShiftedKappaRe (k : ℕ) (s : OffSeed Xi) : ℝ :=
  (cderivIter k Xi (sc s)).re

@[simp] theorem xiShiftedJetAt_eq (k : ℕ) (s : OffSeed Xi) :
    xiShiftedJetAt k s = xiCentralJetAt k s := rfl

@[simp] theorem xiShiftedWindow_eq (k : ℕ) (s : OffSeed Xi) :
    xiShiftedWindow k s = w0At k s := rfl

@[simp] theorem xiShiftedKappaRe_eq (k : ℕ) (s : OffSeed Xi) :
    xiShiftedKappaRe k s = (cderivIter k Xi (sc s)).re := rfl

end XiPacket
end Targets
end Hyperlocal
