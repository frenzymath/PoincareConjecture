import PoincareConjecture.Definitions.M20ThreeDimensionalClassification
import PoincareConjecture.Definitions.Ch09.AsymptoticVolume








set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


structure AsymptoticVolumeRatioSliceData
    (K : AncientKappaSolution n M) (t : ℝ) where
  time_mem : t ≤ 0
  ratio_antitone : ∀ p : M,
    AntitoneMetricBallVolumeRatio (K.flow.metric t) p
  ratio_limit : ∀ p : M,
    HasAsymptoticVolumeRatio (K.flow.metric t) p
  basepoint_independent :
    AsymptoticVolumeRatioBasepointIndependent (K.flow.metric t)

end PoincareConjecture
