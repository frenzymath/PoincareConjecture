import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.FlowMetric








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem relative_limit_base_eq
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier)
    (hconv : Tendsto (fun k ↦ ((L.embedding (σ k)).inverse
      (0, ((G.embedding (σ k)).toFun (0, G.limitFlow.base)).2)).2) atTop
        (𝓝 (f G.limitFlow.base))) :
    f G.limitFlow.base = L.limitFlow.base := by
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let := (L.limitFlow.metricAt 0).toMetricSpace
  apply tendsto_nhds_unique hconv
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hr : 0 < ε / 4 := by positivity
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hσ.tendsto_atTop.eventually
    (eventually_relative_map_smooth C F H G L hGtime hLtime hGcomplete hLcomplete hsource hr))
  refine ⟨N, fun k hk ↦ ?_⟩
  have hp : G.limitFlow.base ∈ G.limitFlow.ballAt 0 (ε / 4) := by
    change G.limitFlow.base ∈ (G.limitFlow.metricAt 0).ball G.limitFlow.base (ε / 4)
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball]
    exact Metric.mem_ball_self hr
  have hball := (hN k hk).1 hp
  change _ ∈ (L.limitFlow.metricAt 0).ball L.limitFlow.base (4 * (ε / 4)) at hball
  rw [← (L.limitFlow.metricAt 0).toMetricSpace_ball, Metric.mem_ball] at hball
  simpa only [show (4 : ℝ) * (ε / 4) = ε by ring] using hball

theorem exists_relative_pointed_flow_diffeomorph
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    (hmetric : ∀ k t, t ∈ Ioo a b → t ∈ Ioo c d →
      (F (G.subsequence k)).metricAt t = (H (L.subsequence k)).metricAt t) :
    letI := (L.limitFlow.metricAt 0).toMetricSpace
    letI := (G.limitFlow.metricAt 0).toMetricSpace
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ e : Diffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier L.limitCarrier.carrier ∞,
        e G.limitFlow.base = L.limitFlow.base ∧
        (∀ t, t ∈ Ioo a b → t ∈ Ioo c d → ∀ x (v w : TangentSpace (𝓡 n) x),
          (L.limitFlow.metricAt t).inner (e x) (mfderiv (𝓡 n) (𝓡 n) e x v)
            (mfderiv (𝓡 n) (𝓡 n) e x w) = (G.limitFlow.metricAt t).inner x v w) ∧
        (∀ Q : Set G.limitCarrier.carrier, IsCompact Q →
          TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
            (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) e atTop Q) ∧
        (∀ Q : Set L.limitCarrier.carrier, IsCompact Q →
          TendstoUniformlyOn (fun k y ↦ ((G.embedding (σ k)).inverse
            (0, ((L.embedding (σ k)).toFun (0, y)).2)).2) e.symm atTop Q) := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  have hm0 := fun k ↦ hmetric k 0 hGtime hLtime
  obtain ⟨σ, hσ, e, _, hconv, hinv⟩ := exists_relative_diffeomorph C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hm0
  refine ⟨σ, hσ, e, ?_, ?_, hconv, hinv⟩
  · exact relative_limit_base_eq C F H G L hGtime hLtime hGcomplete hLcomplete hsource hσ e
      ((hconv {G.limitFlow.base} isCompact_singleton).tendsto_at (mem_singleton _))
  · intro t hGt hLt x v w
    exact relative_limit_metric_inner_eq C F H G L hGtime hLtime hGcomplete hLcomplete
      hsource hm0 hσ e e.contMDiff.continuous hconv t hGt hLt
      (fun k ↦ hmetric k t hGt hLt) x v w

end PoincareConjecture.PointedGeometricConvergence
