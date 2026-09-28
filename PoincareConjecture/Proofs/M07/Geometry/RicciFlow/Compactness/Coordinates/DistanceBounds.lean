import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.IndexedCovering
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric









noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.NormalChartCover

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PseudoMetricSpace M]

theorem chart_lipschitzWith_of_distance_bounds
    {g : ℝ → RiemannianMetric n M} {p : M}
    {T' T A R ρ a b : ℝ} {N : ℕ}
    (C : NormalChartCover g p T' T A R ρ a b N) (i : Fin (N + 1))
    (_hb : 0 ≤ b)
    (hreal : ∀ x y : M, dist x y = ((g 0).edist x y).toReal) :
    LipschitzWith ⟨Real.sqrt b, Real.sqrt_nonneg b⟩
      (fun x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 2) =>
        C.chart i (x : EuclideanSpace ℝ (Fin n))) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := (C.distances i (x : EuclideanSpace ℝ (Fin n)) x.property
    (y : EuclideanSpace ℝ (Fin n)) y.property).2
  rw [← hreal] at hxy
  change dist (C.chart i (x : EuclideanSpace ℝ (Fin n)))
      (C.chart i (y : EuclideanSpace ℝ (Fin n))) ≤
    Real.sqrt b * dist (x : EuclideanSpace ℝ (Fin n))
      (y : EuclideanSpace ℝ (Fin n))
  simpa only [Subtype.dist_eq] using hxy

theorem chart_lower_distance_of_distance_bounds
    {g : ℝ → RiemannianMetric n M} {p : M}
    {T' T A R ρ a b : ℝ} {N : ℕ}
    (C : NormalChartCover g p T' T A R ρ a b N) (i : Fin (N + 1))
    (_ha : 0 < a)
    (hreal : ∀ x y : M, dist x y = ((g 0).edist x y).toReal) :
    ∀ x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 2),
      Real.sqrt a * dist x y ≤
        dist (C.chart i (x : EuclideanSpace ℝ (Fin n)))
          (C.chart i (y : EuclideanSpace ℝ (Fin n))) := by
  intro x y
  have hxy := (C.distances i (x : EuclideanSpace ℝ (Fin n)) x.property
    (y : EuclideanSpace ℝ (Fin n)) y.property).1
  rw [← hreal] at hxy
  simpa only [Subtype.dist_eq] using hxy

end PoincareConjecture.NormalChartCover

namespace PoincareConjecture






theorem NormalChartCover.chart_lipschitzWith_of_flow
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    {F : BasedFlow n T' T C} {A R ρ a b : ℝ} {N : ℕ}
    (cover : @NormalChartCover n C.carrier C.topologicalSpace C.chartedSpace
      C.isManifold
      (@RicciFlow.metric n C.carrier C.topologicalSpace C.chartedSpace
        C.isManifold (Set.Ioo T' T) F.flow)
      F.base T' T A R ρ a b N)
    (i : Fin (N + 1)) (hb : 0 ≤ b) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
    LipschitzWith ⟨Real.sqrt b, Real.sqrt_nonneg b⟩
      (fun x : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 2) =>
        cover.chart i (x : EuclideanSpace ℝ (Fin n))) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
  apply NormalChartCover.chart_lipschitzWith_of_distance_bounds cover i hb
  intro x y
  exact FlowCarrier.dist_metricSpaceOf C (F.flow.metric 0) x y

theorem NormalChartCover.chart_lower_distance_of_flow
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    {F : BasedFlow n T' T C} {A R ρ a b : ℝ} {N : ℕ}
    (cover : @NormalChartCover n C.carrier C.topologicalSpace C.chartedSpace
      C.isManifold
      (@RicciFlow.metric n C.carrier C.topologicalSpace C.chartedSpace
        C.isManifold (Set.Ioo T' T) F.flow)
      F.base T' T A R ρ a b N)
    (i : Fin (N + 1)) (ha : 0 < a) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
    ∀ x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) (ρ / 2),
      Real.sqrt a * dist x y ≤
        dist (cover.chart i (x : EuclideanSpace ℝ (Fin n)))
          (cover.chart i (y : EuclideanSpace ℝ (Fin n))) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
  apply NormalChartCover.chart_lower_distance_of_distance_bounds cover i ha
  intro x y
  exact FlowCarrier.dist_metricSpaceOf C (F.flow.metric 0) x y

end PoincareConjecture
