/-
  Hyperlocal/Transport/Exports.lean

  Referee-facing exports for the Stage–3 transport/Toeplitz layer.
-/

import Hyperlocal.Transport.TACToeplitz

noncomputable section

-- NOTE: We intentionally do NOT open `namespace Hyperlocal.Transport` here,
-- otherwise `export Hyperlocal.Transport ...` becomes a self-export.

export Hyperlocal.Transport
  ( toeplitzR toeplitzL
    toeplitzR_shiftGenerated toeplitzL_shiftGenerated
    parityₗ_comp_toeplitzR
    TACToeplitzR TACToeplitzL
    parityₗ_comp_TACToeplitzR
  )
