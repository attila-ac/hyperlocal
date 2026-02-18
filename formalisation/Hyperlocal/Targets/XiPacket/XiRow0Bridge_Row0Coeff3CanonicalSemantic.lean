/-
REPLACE FILE CONTENT for:
  Hyperlocal/Targets/XiPacket/XiRow0Bridge_Row0Coeff3CanonicalSemantic.lean

POST Move–3 canonical closure:
this file is no longer a semantic insertion point.

It now re-exports the *theorem-level* canonical Row--0 gates
`row0ConvolutionAtRev_w0/wc/wp2/wp3` proved in:

  `XiRow0Bridge_JetLeibnizToRow0ConvolutionRev.lean`

Cycle safety preserved:
* does NOT import Route--B Row0Concrete/Row0Analytic
* only imports Route--C bridge + window definitions.
-/

import Hyperlocal.Targets.XiPacket.XiRow0Bridge_JetLeibnizToRow0ConvolutionRev
import Hyperlocal.Targets.XiPacket.XiWindowDefs

set_option autoImplicit false
noncomputable section

namespace Hyperlocal
namespace Targets
namespace XiPacket

open Complex
open scoped BigOperators

/-!
  ## Canonical Row--0 gates (theorem-level, axiom-free)

  These names remain stable for downstream consumers.
-/

-- Re-export under the original “canonical semantic” surface API.
namespace Row0Coeff3CanonicalSemanticExport
export _root_.Hyperlocal.Targets.XiPacket
  (row0ConvolutionAtRev_w0 row0ConvolutionAtRev_wc
   row0ConvolutionAtRev_wp2 row0ConvolutionAtRev_wp3)
end Row0Coeff3CanonicalSemanticExport

end XiPacket
end Targets
end Hyperlocal
