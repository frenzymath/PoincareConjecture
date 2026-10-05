import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.RicciFlow.Harnack.Theory
import PoincareLib.Geometry.Riemannian.Measure.Calibrated
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Gradient shrinking solitons and their self-similar flows

Ported from Mapher `Definitions/Ch09/ShrinkingSoliton.lean` at
`49331b7d7ecad38f53e4300c3b35d6a84b2cc648`, with declarations unchanged.
Morgan--Tian, Definition 9.41 and Theorem 9.42, pp. 206-208.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-! ## Static hypotheses -/

/-- The scale-invariant volume lower bound in Definition 9.41. -/
def MetricKappaNoncollapsed (g : RiemannianMetric n M)
    (D : LeviCivitaData g) (κ : ℝ) : Prop :=
  0 < κ ∧ ∀ p : M, ∀ r : ℝ, 0 < r →
    (∀ q ∈ g.ball p r, |D.curvatureTensorNorm q| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume g (g.ball p r)

/-- Constant positive sectional curvature, tested on orthonormal pairs. -/
def ConstantPositiveSectionalCurvature (g : RiemannianMetric n M)
    (D : LeviCivitaData g) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
    g.inner x u u = 1 → g.inner x v v = 1 → g.inner x u v = 0 →
      D.sectionalCurvature x u v = c

/-- A complete bounded-curvature non-flat gradient shrinking soliton datum. -/
structure GradientShrinkingSolitonData (n : ℕ) (M : Type u)
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M] where
  metric : RiemannianMetric n M
  connection : LeviCivitaData metric
  dimension : n = 2 ∨ n = 3
  complete : MetricComplete metric
  nonflat : ∃ x : M, connection.curvatureTensorNorm x ≠ 0
  nonnegative_curvature : ∀ x : M,
    LeviCivitaData.NonnegativeCurvatureOperator connection x
  bounded_curvature : ∃ K : ℝ, 0 ≤ K ∧ ∀ x : M,
    |connection.curvatureTensorNorm x| ≤ K
  kappa : ℝ
  kappa_pos : 0 < kappa
  kappa_noncollapsed : MetricKappaNoncollapsed metric connection kappa
  potential : M → ℝ
  potential_C2 : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) 2 potential
  soliton_equation : ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
    connection.ricci x u v + connection.hessian potential x u v =
      (1 / 2 : ℝ) * metric.inner x u v

/-- A diffeomorphism transporting one metric to a positive homothetic copy. -/
structure HomotheticMetricSlice {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (h : RiemannianMetric n M) (scale : ℝ) where
  map : Diffeomorph (𝓡 n) (𝓡 n) M M ∞
  inner_eq : ∀ x : M, ∀ u v : TangentSpace (𝓡 n) x,
    h.inner x u v = scale * g.inner (map x)
      (mfderiv (𝓡 n) (𝓡 n) map x u)
      (mfderiv (𝓡 n) (𝓡 n) map x v)

/-- The self-similar ancient flow built from a shrinking soliton slice. -/
structure ShrinkingSolitonFlow {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (S : GradientShrinkingSolitonData n M) where
  flow : RicciFlow n M (Set.Iio 0)
  at_minus_one : flow.metric (-1) = S.metric
  self_similar : ∀ t : ℝ, t < 0 →
    Nonempty (HomotheticMetricSlice S.metric (flow.metric t) |t|)

/-! ## Model certificates -/

/-- The compact round alternative. -/
structure CompactRoundShrinkingModel {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    {S : GradientShrinkingSolitonData n M}
    (G : ShrinkingSolitonFlow S) where
  compact : CompactSpace M
  round_at_time : ∀ t : ℝ, t < 0 →
    ConstantPositiveSectionalCurvature (G.flow.metric t) (G.flow.connection t)

end PoincareMT
