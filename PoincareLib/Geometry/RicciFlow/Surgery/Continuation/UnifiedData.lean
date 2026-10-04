import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.NonemptyData
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.VanishingData

/-!
Adapted from Mapher `PoincareMT/Definitions/M43UnifiedContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M43 repaired unified continuation data

The unified output stores exactly one branch certificate. A `Sum` keeps the
nonempty and whole-slice-vanishing alternatives constructor-disjoint while
preserving the detailed branch data for downstream schedule rows.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedUnifiedContinuationData
    {F : SurgeryFlowData.{u}} {T : ℝ}
    (I : RepairedContinuationInput F T)
    (branch : RepairedBranchContinuationData I) where
  terminal : Sum (RepairedNonemptyContinuationData I branch)
    (RepairedVanishingContinuationData I branch)

end PoincareMT
