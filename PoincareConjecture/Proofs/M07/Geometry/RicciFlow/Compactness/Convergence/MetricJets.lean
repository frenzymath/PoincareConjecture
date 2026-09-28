import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Embedding.BallTransfer









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}


theorem tendsto_coordinate_metricJet (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (r : ℕ) (a b : Fin n)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target) :
    Tendsto (fun k ↦ iteratedFDeriv ℝ r
      (FlowCarrier.coordinateCoefficient G.limitCarrier q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b) p)
      atTop (𝓝 (iteratedFDeriv ℝ r
        (FlowCarrier.coordinateCoefficient G.limitCarrier q
          (fun t x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w) a b) p)) := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
    (isCompact_singleton (x := (extChartAt (𝓡 n) q).symm p.2))
  have hdom : {p} ⊆ {z | z.1 ∈ Ioo T' T ∧ z.2 ∈ (extChartAt (𝓡 n) q).target ∧
      (extChartAt (𝓡 n) q).symm z.2 ∈ G.exhaustion j} :=
    singleton_subset_iff.mpr ⟨ht, hp, hj (mem_singleton _)⟩
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N, _, hN⟩ := G.pullback_metric_CInfinity q j r {p} isCompact_singleton hdom ε hε
  refine ⟨N, fun k hk ↦ ?_⟩
  simpa only [dist_eq_norm, MetricJet] using hN k hk a b p (mem_singleton p)


theorem tendsto_coordinate_metricJet_apply (G : PointedGeometricConvergence S)
    (q : G.limitCarrier.carrier) (r : ℕ) (a b : Fin n)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (ht : p.1 ∈ Ioo T' T)
    (hp :
      letI : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
        G.limitCarrier.chartedSpace
      p.2 ∈ (extChartAt (𝓡 n) q).target)
    (v : Fin r → ℝ × EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k ↦ iteratedFDeriv ℝ r
      (FlowCarrier.coordinateCoefficient G.limitCarrier q
        (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k)) a b) p v)
      atTop (𝓝 (iteratedFDeriv ℝ r
        (FlowCarrier.coordinateCoefficient G.limitCarrier q
          (fun t x v w ↦ G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v w) a b) p v)) :=
  (continuous_eval_const v).continuousAt.tendsto.comp
    (G.tendsto_coordinate_metricJet q r a b p ht hp)

end PoincareConjecture.PointedGeometricConvergence
