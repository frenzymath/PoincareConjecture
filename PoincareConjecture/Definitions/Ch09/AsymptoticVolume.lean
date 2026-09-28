import PoincareConjecture.Definitions.Ch09.AsymptoticSoliton
import PoincareConjecture.Definitions.Ch04.Pinching
import Mathlib.Topology.Algebra.Order.LiminfLimsup












set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


abbrev PositiveRadius := {r : ℝ // 0 < r}


noncomputable def metricBallVolumeRatio (g : RiemannianMetric n M) (p : M)
    (r : PositiveRadius) : ℝ≥0∞ :=
  calibratedMetricVolume g (g.ball p r.1) / ENNReal.ofReal r.1 ^ n





noncomputable def asymptoticVolumeRatio (g : RiemannianMetric n M) (p : M) : ℝ≥0∞ :=
  sInf (Set.range (metricBallVolumeRatio g p))


def HasAsymptoticVolumeRatio (g : RiemannianMetric n M) (p : M) : Prop :=
  Filter.Tendsto (metricBallVolumeRatio g p) Filter.atTop
    (𝓝 (asymptoticVolumeRatio g p))


def AsymptoticVolumeRatioBasepointIndependent (g : RiemannianMetric n M) : Prop :=
  ∀ p q : M, asymptoticVolumeRatio g p = asymptoticVolumeRatio g q


def AntitoneMetricBallVolumeRatio (g : RiemannianMetric n M) (p : M) : Prop :=
  Antitone (metricBallVolumeRatio g p)





def IsRoundMetricSlice {M3 : Type u} [TopologicalSpace M3]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M3]
    [IsManifold (𝓡 3) ∞ M3] {g : RiemannianMetric 3 M3}
    (D : LeviCivitaData g) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : M3, ∀ u v : TangentSpace (𝓡 3) x,
    D.curvatureTensor x u v u v = c *
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)



def IsRoundAncientKappaSolution {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) : Prop :=
  ∀ t : ℝ, t ≤ 0 → IsRoundMetricSlice (K.flow.connection t)


def AncientAsymptoticVolumeRatioZero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) : Prop :=
  ∀ t : ℝ, t ≤ 0 → ∀ p : M, asymptoticVolumeRatio (K.flow.metric t) p = 0

end PoincareConjecture
