import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Existence
import PoincareLib.Geometry.RicciFlow.Curvature.Construction

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem lGeodesicExistenceAndVariation_from_M04
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (LGeodesicTheory F T τmax) := by
  exact lGeodesicExistenceAndVariation F T τmax hT hτmax hwindow hcurvature
    ricciFlowCurvatureTheory

end PoincareMT
