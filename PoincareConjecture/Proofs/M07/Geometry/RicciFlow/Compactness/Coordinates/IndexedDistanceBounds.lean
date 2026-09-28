import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.Rescaling

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem NormalChartCover.unitBallMap_lipschitzWith_of_flow
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    {F : BasedFlow n T' T C} {A R ρ a b : ℝ} {N : ℕ}
    (cover : @NormalChartCover n C.carrier C.topologicalSpace C.chartedSpace
      C.isManifold
      (@RicciFlow.metric n C.carrier C.topologicalSpace C.chartedSpace
        C.isManifold (Set.Ioo T' T) F.flow)
      F.base T' T A R ρ a b N)
    (i : Fin (N + 1)) (hρ : 0 < ρ) (_hb : 0 ≤ b) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
    LipschitzWith ⟨Real.sqrt b * (ρ / 2),
      mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (half_pos hρ))⟩
      (cover.unitBallMap i) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hxy := (cover.unitBallMap_distances hρ i x y).2
  change dist (cover.unitBallMap i x) (cover.unitBallMap i y) ≤
    (Real.sqrt b * (ρ / 2)) * dist x y
  simpa only [FlowCarrier.dist_metricSpaceOf] using hxy

theorem NormalChartCover.unitBallMap_lower_distance_of_flow
    {n : ℕ} {T' T : ℝ} {C : FlowCarrier n}
    {F : BasedFlow n T' T C} {A R ρ a b : ℝ} {N : ℕ}
    (cover : @NormalChartCover n C.carrier C.topologicalSpace C.chartedSpace
      C.isManifold
      (@RicciFlow.metric n C.carrier C.topologicalSpace C.chartedSpace
        C.isManifold (Set.Ioo T' T) F.flow)
      F.base T' T A R ρ a b N)
    (i : Fin (N + 1)) (hρ : 0 < ρ) (_ha : 0 < a) :
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
    letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
    ∀ x y : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      (Real.sqrt a * (ρ / 2)) * dist x y ≤
        dist (cover.unitBallMap i x) (cover.unitBallMap i y) := by
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : MetricSpace C.carrier := C.metricSpaceOf (F.flow.metric 0)
  intro x y
  have hxy := (cover.unitBallMap_distances hρ i x y).1
  simpa only [FlowCarrier.dist_metricSpaceOf] using hxy

end PoincareConjecture
