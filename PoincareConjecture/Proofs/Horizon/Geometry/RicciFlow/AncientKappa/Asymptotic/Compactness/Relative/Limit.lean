import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.UniformGluing








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology NNReal

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem exists_relative_continuous_limit
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k,
      (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0) :
    letI := (L.limitFlow.metricAt 0).toMetricSpace
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f : G.limitCarrier.carrier → L.limitCarrier.carrier,
      Continuous f ∧ ∀ K : Set G.limitCarrier.carrier, IsCompact K →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) f atTop K := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let Q (i : ℕ) := closure (G.exhaustion i)
  have hQ (i : ℕ) : IsCompact (Q i) := G.exhaustion_compactClosure i
  have hbound (i : ℕ) : ∃ r : ℝ, 0 < r ∧ Q i ⊆ G.limitFlow.ballAt 0 r := by
    obtain ⟨r, hr⟩ := (hQ i).isBounded.subset_ball G.limitFlow.base
    have hbase : G.limitFlow.base ∈ Q i := subset_closure (G.base_in_exhaustion i)
    have hrpos : 0 < r := by simpa only [Metric.mem_ball, dist_self] using hr hbase
    refine ⟨r, hrpos, ?_⟩
    change Q i ⊆ (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball]
    exact hr
  choose r hr hQr using hbound
  obtain ⟨σ, hσ, f, hf, hconv⟩ := exists_common_relative_uniformSubsequence C F H G L
    hGtime hLtime hGcomplete hLcomplete hsource hmetric Q hQ r hr hQr
  refine ⟨σ, hσ, ?_⟩
  apply exists_continuous_uniformLimit_of_compact_extraction _ Q _ _ f hf hconv
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (show x ∈ ⋃ i, G.exhaustion i by
      rw [G.exhaustion_covers]
      exact mem_univ x)
    exact ⟨i, Filter.mem_of_superset ((G.exhaustion_open i).mem_nhds hi) subset_closure⟩
  · intro K hK
    obtain ⟨i, hi⟩ := G.exists_exhaustion_superset hK
    exact ⟨i, hi.trans subset_closure⟩

end PoincareConjecture.PointedGeometricConvergence
