import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MetricComparison








set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}


theorem eventually_pullback_inner_upper_on_compactTime
    (G : PointedGeometricConvergence S) {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K)
    {J : Set ℝ} (hJ : IsCompact J) (hJT : J ⊆ Ioo T' T) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ t ∈ J, ∀ x ∈ K, ∀ v : G.limitCarrier.tangent x,
      pullbackInnerValue G.limitFlow (S.flow (G.subsequence k)) (G.embedding k) t x v v ≤
        (1 + ε) * G.limitCarrier.metricInner (G.limitFlow.metricAt t) x v v := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hK
  obtain ⟨N, _, hN⟩ := G.pullback_metric_converges j K J hK hj hJ hJT ε hε
  filter_upwards [eventually_ge_atTop N] with k hk t ht x hx v
  have h := (abs_le.mp (G.abs_pullback_inner_sub_le k t x
    (hN k hk t ht x hx) v)).2
  linarith



theorem eventually_pullback_tangentNorm_upper_on_compactTime
    (G : PointedGeometricConvergence S) {K : Set G.limitCarrier.carrier}
    (hK : @IsCompact G.limitCarrier.carrier G.limitCarrier.topologicalSpace K)
    {J : Set ℝ} (hJ : IsCompact J) (hJT : J ⊆ Ioo T' T) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k : ℕ in atTop, ∀ t ∈ J, ∀ x ∈ K, ∀ v : G.limitCarrier.tangent x,
      Real.sqrt (pullbackInnerValue G.limitFlow (S.flow (G.subsequence k))
        (G.embedding k) t x v v) ≤ C * G.limitCarrier.metricNorm (G.limitFlow.metricAt t) x v := by
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier :=
    G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  have hCpos : 0 < C := zero_lt_one.trans hC
  filter_upwards [G.eventually_pullback_inner_upper_on_compactTime hK hJ hJT
    (by nlinarith : 0 < C ^ 2 - 1)] with k hk t ht x hx v
  have h := hk t ht x hx v
  rw [show 1 + (C ^ 2 - 1) = C ^ 2 by ring] at h
  have hs := Real.sqrt_le_sqrt h
  rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hCpos.le] at hs
  exact hs

end PoincareConjecture.PointedGeometricConvergence
