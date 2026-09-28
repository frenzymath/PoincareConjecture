import PoincareConjecture.Definitions.M21AsymptoticVolume
import PoincareConjecture.Statements.Ch01.CurvatureCalculus








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ}



def AsymptoticVolumeRatioPredecessors (n : ℕ) : Prop :=
  ∀ (M : Type u) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g), D.CurvatureTensorCalculus



structure AsymptoticVolumeRatioTheory (n : ℕ) : Prop where
  slice : ∀ {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) (t : ℝ), t ≤ 0 →
    Nonempty (AsymptoticVolumeRatioSliceData K t)

end PoincareConjecture
