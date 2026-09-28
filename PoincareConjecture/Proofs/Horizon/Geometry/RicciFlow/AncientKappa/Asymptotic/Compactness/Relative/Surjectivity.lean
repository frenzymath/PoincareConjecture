import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Isometry








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology NNReal

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

theorem relative_limit_surjective
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
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier) (hf : Continuous f)
    (hconv : letI := (L.limitFlow.metricAt 0).toMetricSpace
      ∀ K : Set G.limitCarrier.carrier, IsCompact K →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) f atTop K) :
    Function.Surjective f := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  intro y
  let r := dist L.limitFlow.base y + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hy : y ∈ L.limitFlow.ballAt 0 r := by
    change y ∈ (L.limitFlow.metricAt 0).ball L.limitFlow.base r
    rw [← (L.limitFlow.metricAt 0).toMetricSpace_ball, Metric.mem_ball, dist_comm]
    dsimp [r]
    linarith
  let xseq (k : ℕ) := ((G.embedding (σ k)).inverse
    (0, ((L.embedding (σ k)).toFun (0, y)).2)).2
  let K := closure (G.limitFlow.ballAt 0 (4 * r))
  have hK : IsCompact K :=
    (G.limitFlow.metricAt 0).isCompact_closure_ball_of_metricComplete hGcomplete
      G.limitFlow.base (4 * r)
  have hxK : ∀ᶠ k in atTop, xseq k ∈ K := by
    filter_upwards [hσ.tendsto_atTop.eventually (eventually_relative_map_smooth C H F L G
      hLtime hGtime hLcomplete hGcomplete (fun k r ↦ (hsource k r).symm) hr)] with k hk
    exact subset_closure (hk.1 hy)
  obtain ⟨x, _, τ, hτ, hlim⟩ := hK.tendsto_subseq' hxK.frequently
  have huc : TendstoUniformlyOn (fun k z ↦ ((L.embedding (σ (τ k))).inverse
      (0, ((G.embedding (σ (τ k))).toFun (0, z)).2)).2) f atTop K := by
    intro u hu
    exact hτ.tendsto_atTop.eventually (hconv K hK u hu)
  have hcompose := huc.tendsto_comp hf.continuousWithinAt
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, hτ.tendsto_atTop.eventually hxK⟩)
  have heq : (fun k ↦ ((L.embedding (σ (τ k))).inverse
      (0, ((G.embedding (σ (τ k))).toFun (0, xseq (τ k))).2)).2) =ᶠ[atTop]
      (fun _ ↦ y) := by
    filter_upwards [(hσ.comp hτ).tendsto_atTop.eventually
      (eventually_relative_left_inverse C H F L G hLtime hGtime hLcomplete hGcomplete
        (fun k r ↦ (hsource k r).symm) hr)] with k hk
    exact hk y hy
  refine ⟨x, ?_⟩
  exact tendsto_nhds_unique hcompose (tendsto_const_nhds.congr' heq.symm)

theorem exists_relative_isometryEquiv
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
    letI := (G.limitFlow.metricAt 0).toMetricSpace
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ e : G.limitCarrier.carrier ≃ᵢ L.limitCarrier.carrier,
      ∀ K : Set G.limitCarrier.carrier, IsCompact K →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) e atTop K := by
  classical
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  obtain ⟨σ, hσ, f, hf, hconv⟩ := exists_relative_isometric_limit C F H G L
    hGtime hLtime hGcomplete hLcomplete hsource hmetric
  have hsurj := relative_limit_surjective C F H G L hGtime hLtime hGcomplete hLcomplete
    hsource hσ f hf.continuous hconv
  let e : G.limitCarrier.carrier ≃ᵢ L.limitCarrier.carrier :=
    { Equiv.ofBijective f ⟨hf.injective, hsurj⟩ with isometry_toFun := hf }
  exact ⟨σ, hσ, e, hconv⟩

end PoincareConjecture.PointedGeometricConvergence
