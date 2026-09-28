import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Surjectivity







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem tendstoUniformlyOn_inverse_relative_limit
    {n : ℕ} (C : FlowCarrier.{0} n) {a b c d : ℝ}
    (F : ℕ → BasedFlow n a b C) (H : ℕ → BasedFlow n c d C)
    (G : PointedGeometricConvergence ⟨fun _ ↦ C, F⟩)
    (L : PointedGeometricConvergence ⟨fun _ ↦ C, H⟩)
    (hGtime : a < 0 ∧ 0 < b) (hLtime : c < 0 ∧ 0 < d)
    (hGcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (hLcomplete : L.limitCarrier.metricComplete (L.limitFlow.metricAt 0))
    (hsource : ∀ k r, (F (G.subsequence k)).ballAt 0 r =
      (H (L.subsequence k)).ballAt 0 r)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) :
    letI := (L.limitFlow.metricAt 0).toMetricSpace
    letI := (G.limitFlow.metricAt 0).toMetricSpace
    ∀ e : G.limitCarrier.carrier ≃ᵢ L.limitCarrier.carrier,
      (∀ Q : Set G.limitCarrier.carrier, IsCompact Q →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) e atTop Q) →
      ∀ K : Set L.limitCarrier.carrier, IsCompact K →
        TendstoUniformlyOn (fun k y ↦ ((G.embedding (σ k)).inverse
          (0, ((L.embedding (σ k)).toFun (0, y)).2)).2) e.symm atTop K := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  intro e hconv K hK
  obtain ⟨r₀, hr₀⟩ := hK.isBounded.subset_ball L.limitFlow.base
  let r := max r₀ 1
  have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hKr : K ⊆ L.limitFlow.ballAt 0 r := by
    change K ⊆ (L.limitFlow.metricAt 0).ball L.limitFlow.base r
    rw [← (L.limitFlow.metricAt 0).toMetricSpace_ball]
    exact hr₀.trans (Metric.ball_subset_ball (le_max_left _ _))
  let Q := closure (G.limitFlow.ballAt 0 (4 * r))
  have hQ : IsCompact Q :=
    (G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hGcomplete
      G.limitFlow.base (4 * r)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hconv Q hQ) ε hε,
    hσ.tendsto_atTop.eventually (eventually_relative_map_smooth C H F L G hLtime hGtime
      hLcomplete hGcomplete (fun k r ↦ (hsource k r).symm) hr),
    hσ.tendsto_atTop.eventually (eventually_relative_left_inverse C H F L G hLtime hGtime
      hLcomplete hGcomplete (fun k r ↦ (hsource k r).symm) hr)] with k hk hmap hinv y hy
  let x := ((G.embedding (σ k)).inverse (0, ((L.embedding (σ k)).toFun (0, y)).2)).2
  have hx : x ∈ Q := subset_closure (hmap.1 (hKr hy))
  have heq : ((L.embedding (σ k)).inverse
      (0, ((G.embedding (σ k)).toFun (0, x)).2)).2 = y := hinv y (hKr hy)
  change dist (e.symm y) x < ε
  rw [← e.dist_eq, e.apply_symm_apply, dist_comm]
  simpa only [heq] using hk x hx

end PoincareConjecture.PointedGeometricConvergence
