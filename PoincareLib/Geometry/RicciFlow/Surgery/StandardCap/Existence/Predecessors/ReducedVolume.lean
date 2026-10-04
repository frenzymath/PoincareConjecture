import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Monotonicity
import PoincareLib.Geometry.RicciFlow.Curvature.Construction
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.LGeodesics
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.ReducedLength

/-! Source predecessor applications; existing geometric proofs are reused. -/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]

theorem reducedVolumeMonotonicity_from_M08_M09
    {J : Set ℝ} [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (T τmax : ℝ) (hT : T ∈ J) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T)) :
    Nonempty (ReducedVolumeTheory F T τmax) := by
  rcases lGeodesicExistenceAndVariation_from_M04 F T τmax hT hτmax hwindow hcurvature with ⟨hL⟩
  rcases reducedLengthDifferentialInequalities_from_M04_M08 F T τmax
      hT hτmax hwindow hcurvature with ⟨hDifferential⟩
  exact reducedVolumeMonotonicity F T τmax hT hτmax hwindow hcurvature hL hDifferential

end PoincareMT
