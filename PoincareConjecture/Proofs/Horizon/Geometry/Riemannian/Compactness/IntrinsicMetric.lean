import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Exhaustion

noncomputable section
set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

@[reducible] def toMetricSpace (g : RiemannianMetric n M) : MetricSpace M := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  exact EMetricSpace.toMetricSpace g.edist_ne_top

@[simp] theorem toMetricSpace_dist (g : RiemannianMetric n M) (x y : M) :
    @dist M g.toMetricSpace.toPseudoMetricSpace.toDist x y = (g.edist x y).toReal := rfl

@[simp] theorem toMetricSpace_edist (g : RiemannianMetric n M) (x y : M) :
    @EDist.edist M g.toMetricSpace.toPseudoMetricSpace.toEDist x y = g.edist x y := rfl

theorem completeSpace_toMetricSpace (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) :
    letI := g.toMetricSpace
    CompleteSpace M := hcomplete

theorem toMetricSpace_ball (g : RiemannianMetric n M) (p : M) (r : ℝ) :
    letI := g.toMetricSpace
    Metric.ball p r = g.ball p r := by
  let := g.toMetricSpace
  ext q
  rw [Metric.mem_ball, dist_comm, toMetricSpace_dist]
  change (g.edist p q).toReal < r ↔ g.edist p q < ENNReal.ofReal r
  rw [← ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (g.edist_ne_top p q)]

theorem toMetricSpace_closedBall (g : RiemannianMetric n M) (p : M)
    {r : ℝ} (hr : 0 ≤ r) :
    letI := g.toMetricSpace
    Metric.closedBall p r = {q | g.edist p q ≤ ENNReal.ofReal r} := by
  let := g.toMetricSpace
  ext q
  rw [Metric.mem_closedBall, dist_comm, toMetricSpace_dist]
  change (g.edist p q).toReal ≤ r ↔ g.edist p q ≤ ENNReal.ofReal r
  rw [← ENNReal.ofReal_le_ofReal_iff hr,
    ENNReal.ofReal_toReal (g.edist_ne_top p q)]

theorem properSpace_toMetricSpace (g : RiemannianMetric n M)
    (hcomplete : MetricComplete g) :
    letI := g.toMetricSpace
    ProperSpace M := by
  let := g.toMetricSpace
  constructor
  intro p r
  by_cases hr : 0 ≤ r
  · rw [g.toMetricSpace_closedBall p hr]
    exact g.isCompact_closedBall_of_metricComplete hcomplete p r
  · rw [Metric.closedBall_eq_empty.mpr (lt_of_not_ge hr)]
    exact isCompact_empty

theorem approximate_split_toMetricSpace (g : RiemannianMetric n M)
    (x y : M) {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε) :
    letI := g.toMetricSpace
    r < dist x y → ∃ z, dist x z = r ∧ dist z y < dist x y - r + ε := by
  let := g.toMetricSpace
  intro hry
  obtain ⟨z, hz, _, hzy⟩ :=
    g.exists_approximate_distance_split x y (g.edist_ne_top x y) hr hε hry
  refine ⟨z, ?_, hzy⟩
  rw [toMetricSpace_dist, hz, ENNReal.toReal_ofReal hr.le]

end PoincareConjecture.RiemannianMetric
