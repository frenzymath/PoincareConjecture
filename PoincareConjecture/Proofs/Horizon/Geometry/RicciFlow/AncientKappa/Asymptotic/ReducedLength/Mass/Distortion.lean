import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Inheritance.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.EmbeddingIntegral


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem eventually_lintegral_sourcePoint_image_bounds
    (G : AncientCompactTimeConvergence S) {t C : ℝ} (ht : t < 0) (hC : 1 < C)
    {V : Set G.limit.carrier.carrier} (hV : IsOpen V) (hcompact : IsCompact (closure V))
    (F : ℕ → M → ℝ≥0∞) (hF : ∀ k, Continuous (F k)) :
    ∀ᶠ k in atTop,
      (∫⁻ y in G.sourcePoint k '' V, F k y
          ∂((S.rescaling (G.subsequence k)).flow.metric t).volumeMeasure) ≤
        ENNReal.ofReal C ^ n * ∫⁻ x in V, F k (G.sourcePoint k x)
          ∂(G.limit.flow.metric t).volumeMeasure ∧
      (∫⁻ x in V, F k (G.sourcePoint k x) ∂(G.limit.flow.metric t).volumeMeasure) ≤
        ENNReal.ofReal C ^ n * ∫⁻ y in G.sourcePoint k '' V, F k y
          ∂((S.rescaling (G.subsequence k)).flow.metric t).volumeMeasure := by
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j] with k hk hkt hjk
  let g := G.limit.flow.metric t
  let h := (S.rescaling (G.subsequence k)).flow.metric t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) hkt
  have hVe : V ⊆ e.source := subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := fun x hx =>
    ((G.embedding k).spatialMap_contMDiffAt_of_time_nhds
      (G.exhaustion_open k) hkt hx).of_le (by simp) |>.contMDiffWithinAt
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := by
    rintro _ ⟨x, hx, rfl⟩
    have hh := (G.embedding k).spatialInverse_contMDiffAt (G.exhaustion_open k) hkt hx
    exact (hh.of_le (by simp)).contMDiffWithinAt
  have hup : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v :=
    fun x hx v => (hk x (subset_closure hx) v).1
  have hlo : ∀ x ∈ V, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) :=
    fun x hx v => (hk x (subset_closure hx) v).2
  have heq : EqOn (G.sourcePoint k) e V :=
    fun x hx => G.sourcePoint_eq_at k (mem_of_mem_nhds hkt) (hVe hx)
  have himage : G.sourcePoint k '' V = e '' V := heq.image_eq
  have hint : (∫⁻ x in V, F k (G.sourcePoint k x) ∂g.volumeMeasure) =
      ∫⁻ x in V, F k (e x) ∂g.volumeMeasure :=
    setLIntegral_congr_fun hV.measurableSet (fun x hx => congrArg (F k) (heq hx))
  change (∫⁻ y in G.sourcePoint k '' V, F k y ∂h.volumeMeasure) ≤
      ENNReal.ofReal C ^ n * (∫⁻ x in V, F k (G.sourcePoint k x) ∂g.volumeMeasure) ∧
    (∫⁻ x in V, F k (G.sourcePoint k x) ∂g.volumeMeasure) ≤
      ENNReal.ofReal C ^ n * (∫⁻ y in G.sourcePoint k '' V, F k y ∂h.volumeMeasure)
  rw [himage, hint]
  exact ⟨g.lintegral_image_le_of_tangentNorm_le h e hV hVe he (zero_lt_one.trans hC) hup
      (hF k).continuousOn,
    g.lintegral_le_image_of_tangentNorm_le h e hV hVe he hei (zero_lt_one.trans hC) hlo
      (hF k).continuousOn⟩

theorem eventually_source_base_ball_subset_sourcePoint_image_ball
    (G : AncientCompactTimeConvergence S) {t r C : ℝ}
    (ht : t < 0) (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      ((S.rescaling (G.subsequence k)).flow.metric t).ball (S.base (G.subsequence k)) r ⊆
        G.sourcePoint k '' (G.limit.flow.metric t).ball G.limit.base (C * r) := by
  have hcompact := (G.limit.flow.metric t).isCompact_closure_ball_of_metricComplete
    (G.limit.complete t ht) G.limit.base (C * r)
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_source_ball_subset_image_ball ht G.limit.base hr hC,
    eventually_timeWindow_mem_nhds ht, eventually_ge_atTop j] with k hk hkt hjk
  have hbase := G.sourcePoint_eq_at k (mem_of_mem_nhds hkt) (G.base_in_exhaustion k)
  rw [G.sourcePoint_base] at hbase
  rw [← hbase] at hk
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hk hy
  refine ⟨x, hx, ?_⟩
  rw [G.sourcePoint_eq_at k (mem_of_mem_nhds hkt)
    (G.exhaustion_monotone hjk (hj (subset_closure hx)))]
  exact hxy

end PoincareConjecture.AncientCompactTimeConvergence
