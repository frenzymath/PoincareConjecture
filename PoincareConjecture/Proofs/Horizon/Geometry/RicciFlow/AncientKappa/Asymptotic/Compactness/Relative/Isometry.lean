import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Limit
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.Inverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology NNReal

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space carrierPreconnected

private theorem ennreal_le_of_forall_sq_mul {a b : ENNReal}
    (h : ∀ D : ℝ, 1 < D → a ≤ ENNReal.ofReal (D ^ 2) * b) : a ≤ b := by
  have hlim : Tendsto (fun D : ℝ ↦ ENNReal.ofReal (D ^ 2))
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ENNReal)) := by
    have hc : Continuous (fun D : ℝ ↦ ENNReal.ofReal (D ^ 2)) :=
      ENNReal.continuous_ofReal.comp (continuous_id.pow 2)
    simpa only [one_pow, ENNReal.ofReal_one] using (hc.tendsto 1).mono_left
      (nhdsWithin_le_nhds (s := Ioi (1 : ℝ)))
  have hmul := ENNReal.Tendsto.mul_const hlim (b := b) (Or.inl one_ne_zero)
  rw [one_mul] at hmul
  apply ge_of_tendsto hmul
  filter_upwards [self_mem_nhdsWithin] with D hD
  exact h D hD

theorem relative_limit_preserves_edist
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
      (F (G.subsequence k)).metricAt 0 = (H (L.subsequence k)).metricAt 0)
    {σ : ℕ → ℕ} (hσ : StrictMono σ)
    (f : G.limitCarrier.carrier → L.limitCarrier.carrier)
    (hconv : ∀ x, Tendsto (fun k ↦ ((L.embedding (σ k)).inverse
      (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) atTop (𝓝 (f x)))
    (x y : G.limitCarrier.carrier) :
    (L.limitFlow.metricAt 0).edist (f x) (f y) = (G.limitFlow.metricAt 0).edist x y := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  let r := dist G.limitFlow.base x + dist G.limitFlow.base y + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hx : x ∈ G.limitFlow.ballAt 0 r := by
    change x ∈ (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball, Metric.mem_ball, dist_comm]
    dsimp [r]
    linarith [(G.limitFlow.metricAt 0).edist G.limitFlow.base y |>.toReal_nonneg]
  have hy : y ∈ G.limitFlow.ballAt 0 r := by
    change y ∈ (G.limitFlow.metricAt 0).ball G.limitFlow.base r
    rw [← (G.limitFlow.metricAt 0).toMetricSpace_ball, Metric.mem_ball, dist_comm]
    dsimp [r]
    linarith [(G.limitFlow.metricAt 0).edist G.limitFlow.base x |>.toReal_nonneg]
  have hlim := (hconv x).edist (hconv y)
  have hb (D : ℝ) (hD : 1 < D) := hσ.tendsto_atTop.eventually
    (eventually_relative_edist_bounds C F H G L hGtime hLtime
      hGcomplete hLcomplete hsource hmetric hr hD)
  apply le_antisymm
  · apply ennreal_le_of_forall_sq_mul
    intro D hD
    apply le_of_tendsto hlim
    filter_upwards [hb D hD] with k hk
    exact (hk x hx y hy).1
  · apply ennreal_le_of_forall_sq_mul
    intro D hD
    apply ge_of_tendsto (ENNReal.Tendsto.const_mul hlim (a := ENNReal.ofReal (D ^ 2))
      (Or.inr ENNReal.ofReal_ne_top))
    filter_upwards [hb D hD] with k hk
    exact (hk x hx y hy).2

theorem exists_relative_isometric_limit
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
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ f : G.limitCarrier.carrier → L.limitCarrier.carrier,
      Isometry f ∧ ∀ K : Set G.limitCarrier.carrier, IsCompact K →
        TendstoUniformlyOn (fun k x ↦ ((L.embedding (σ k)).inverse
          (0, ((G.embedding (σ k)).toFun (0, x)).2)).2) f atTop K := by
  let := (L.limitFlow.metricAt 0).toMetricSpace
  let := (G.limitFlow.metricAt 0).toMetricSpace
  obtain ⟨σ, hσ, f, _, hconv⟩ := exists_relative_continuous_limit C F H G L
    hGtime hLtime hGcomplete hLcomplete hsource hmetric
  refine ⟨σ, hσ, f, ?_, hconv⟩
  intro x y
  exact relative_limit_preserves_edist C F H G L hGtime hLtime
    hGcomplete hLcomplete hsource hmetric hσ f
    (fun z ↦ (hconv {z} isCompact_singleton).tendsto_at (mem_singleton z)) x y

end PoincareConjecture.PointedGeometricConvergence
