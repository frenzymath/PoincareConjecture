import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Soliton
import PoincareLib.Topology.Manifold.NeckCap
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistance
import PoincareLib.Geometry.RicciFlow.Blowup.DenseTime
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Blowup
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Theory

open scoped PoincareMT.FinalSource
/-!
# Applied services for deep-horn selection

These checked applications supply M04 and M19's dimension-two prerequisites once,
apply M28 before supplying M29, and retain M30's actual short/long services.
M32 still constructs the geometric controls on its own blowup sequence.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Apply the earlier milestone theorems to supply all four M32 services.
M04 supplies scalar evolution on the actual neck geometry.
The M19 service classifies the actual input solution. The M29 service already
contains the M28 estimates, with no remaining predecessor premise. -/
theorem m32HornSelectionPredecessors : RepairedHornSelectionPredecessors.{u} := by
  refine {
    m04 := ricciFlowCurvatureTheory
    m19_round := ?_
    m29 := m29GeneralizedBoundedDistance
      (m28BoundedDistance ⟨ricciFlowCurvatureTheory, m25NeckCapTopology⟩)
    m30 := m30ControlledGeneralizedBlowupLimitsFromMilestones
  }
  intro N _ _ _ _ _ _ _ _ _ K
  exact (twoDimensionalClassificationTheory
    (m20TwoDimensionalPredecessors (N := N))).ancient_classification K

/-- Theorem 11.31 and Corollary 11.36 with the M04/M19/M29/M30 service arguments
supplied by their producing theorems. The geometric proof is supplied by
`m32HornSelection`; this application retains the lower services' dependencies. -/
theorem m32HornSelectionFromMilestones : RepairedHornSelectionTheory.{u} :=
  m32HornSelection m32HornSelectionPredecessors

end PoincareMT
