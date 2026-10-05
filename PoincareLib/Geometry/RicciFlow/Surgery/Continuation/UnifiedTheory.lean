import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.UnifiedData
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.NonemptyTheory
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.VanishingTheory

/-!
Adapted from Mapher `PoincareMT/Statements/M43UnifiedContinuation.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M43 repaired unified continuation statement

The M41 and M42 providers select the appropriate constructor on one fixed
M33 continuation by inspecting its supplied controlled-core status. This is
a logical branch assembly; continuation existence remains an M33 obligation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedUnifiedContinuationTheory : Prop where
  continuation : RepairedNonemptyContinuationTheory.{u} →
    RepairedVanishingContinuationTheory.{u} →
    ∀ {F : SurgeryFlowData.{u}} {T : ℝ},
    ∀ (I : RepairedContinuationInput F T) (branch : RepairedBranchContinuationData I),
      Nonempty (RepairedUnifiedContinuationData I branch)

end PoincareMT
