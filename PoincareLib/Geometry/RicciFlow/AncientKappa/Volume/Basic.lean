import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Calibrated ball ratios and ancient asymptotic volume

Declaration bodies from `PoincareMT/Definitions/Ch09/AsymptoticVolume.lean`
at Mapher commit `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.
Morgan--Tian, Chapter 9, Sections 5--6, pp. 219--222.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- A positive radius, used to avoid the singular zero-radius denominator. -/
abbrev PositiveRadius := {r : ℝ // 0 < r}

/-- Calibrated volume ratio of a positive-radius metric ball. -/
noncomputable def metricBallVolumeRatio (g : RiemannianMetric n M) (p : M)
    (r : PositiveRadius) : ℝ≥0∞ :=
  calibratedMetricVolume g (g.ball p r.1) / ENNReal.ofReal r.1 ^ n

/-- The asymptotic volume ratio defined from all positive-radius ratios.

For nonnegative Ricci curvature the Bishop--Gromov theorem identifies this
infimum with the limit as the radius tends to infinity. -/
noncomputable def asymptoticVolumeRatio (g : RiemannianMetric n M) (p : M) : ℝ≥0∞ :=
  sInf (Set.range (metricBallVolumeRatio g p))

/-- The explicit limit statement for an asymptotic volume ratio. -/
def HasAsymptoticVolumeRatio (g : RiemannianMetric n M) (p : M) : Prop :=
  Filter.Tendsto (metricBallVolumeRatio g p) Filter.atTop
    (𝓝 (asymptoticVolumeRatio g p))

/-- Base-point independence of the asymptotic volume ratio. -/
def AsymptoticVolumeRatioBasepointIndependent (g : RiemannianMetric n M) : Prop :=
  ∀ p q : M, asymptoticVolumeRatio g p = asymptoticVolumeRatio g q

/-- The ratio is non-increasing in the radius, as in Bishop--Gromov. -/
def AntitoneMetricBallVolumeRatio (g : RiemannianMetric n M) (p : M) : Prop :=
  Antitone (metricBallVolumeRatio g p)

/-- Constant positive sectional curvature on one metric slice.

The four-tensor identity avoids choosing a frame and is equivalent to the
usual constant-sectional-curvature condition for a Riemannian metric. -/
def IsRoundMetricSlice {M3 : Type u} [TopologicalSpace M3]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M3]
    [IsManifold (𝓡 3) ∞ M3] {g : RiemannianMetric 3 M3}
    (D : LeviCivitaData g) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : M3, ∀ u v : TangentSpace (𝓡 3) x,
    D.curvatureTensor x u v u v = c *
      (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2)

/-- A three-dimensional ancient solution is round when every time slice has
constant positive sectional curvature. -/
def IsRoundAncientKappaSolution {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution 3 M) : Prop :=
  ∀ t : ℝ, t ≤ 0 → IsRoundMetricSlice (K.flow.connection t)

/-- The all-time, all-basepoint vanishing conclusion for Theorem 9.59. -/
def AncientAsymptoticVolumeRatioZero {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (K : AncientKappaSolution n M) : Prop :=
  ∀ t : ℝ, t ≤ 0 → ∀ p : M, asymptoticVolumeRatio (K.flow.metric t) p = 0

end PoincareMT
