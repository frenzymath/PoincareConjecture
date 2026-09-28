import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Embedding.CompactBallTransfer
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.MetricMonotonicity
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {a b : ℝ} {S : PointedFlowSequence n a b}




theorem exists_pos_eventually_embedding_edist_le_of_ricci_nonneg
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K)
    {J : ℕ → Set ℝ} (F : ∀ k, RicciFlow n (S.carrier k).carrier (J k))
    {s t : ℝ} (hst : s ≤ t)
    (hmetric : ∀ᶠ k in atTop, (S.flow k).metricAt 0 = (F k).metric s)
    (htime : ∀ᶠ k in atTop, Icc s t ⊆ interior (J k))
    (hRic : ∀ᶠ k in atTop, ∀ u ∈ Icc s t, ∀ x : (S.carrier k).carrier,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ ((F k).connection u).ricci x v v) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      ((F (G.subsequence k)).metric t).edist (S.flow (G.subsequence k)).base
        (((G.embedding k).toFun (0, x)).2) ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR, hbound⟩ :=
    G.exists_pos_eventually_image_subset_ballAt hzero hzero hcomplete hK
  refine ⟨R, hR, ?_⟩
  filter_upwards [hbound,
    G.subsequence_strictMono.tendsto_atTop.eventually hmetric,
    G.subsequence_strictMono.tendsto_atTop.eventually htime,
    G.subsequence_strictMono.tendsto_atTop.eventually hRic] with k hk hm ht hRic
  intro x hx
  have hsource := hk (mem_image_of_mem (fun y => ((G.embedding k).toFun (0, y)).2) hx)
  change (((G.embedding k).toFun (0, x)).2) ∈
    ((S.flow (G.subsequence k)).metricAt 0).ball (S.flow (G.subsequence k)).base R
    at hsource
  rw [hm] at hsource
  exact ((F (G.subsequence k)).ball_subset_ball_of_ricci_nonneg ht
    (S.flow (G.subsequence k)).base R ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    (fun u hu y _ v => hRic u hu y v) hsource).le




theorem exists_pos_eventually_embedding_edist_le_of_isometric_diffeomorph
    (G : PointedGeometricConvergence S) (hzero : a < 0 ∧ 0 < b)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K)
    (C : ℕ → FlowCarrier.{u} n) {J : ℕ → Set ℝ}
    (F : ∀ k, RicciFlow n (C k).carrier (J k))
    (e : ∀ k, (S.carrier k).carrier ≃ₘ⟮𝓡 n, 𝓡 n⟯ (C k).carrier)
    {s t : ℝ} (hst : s ≤ t)
    (hmetric : ∀ᶠ k in atTop, ∀ (x : (S.carrier k).carrier)
      (v w : TangentSpace (𝓡 n) x),
        ((S.flow k).metricAt 0).inner x v w = ((F k).metric s).inner (e k x)
          (mfderiv (𝓡 n) (𝓡 n) (e k) x v) (mfderiv (𝓡 n) (𝓡 n) (e k) x w))
    (htime : ∀ᶠ k in atTop, Icc s t ⊆ interior (J k))
    (hRic : ∀ᶠ k in atTop, ∀ u ∈ Icc s t, ∀ x : (C k).carrier,
      ∀ v : TangentSpace (𝓡 n) x, 0 ≤ ((F k).connection u).ricci x v v) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      ((F (G.subsequence k)).metric t).edist
        (e (G.subsequence k) (S.flow (G.subsequence k)).base)
        (e (G.subsequence k) (((G.embedding k).toFun (0, x)).2)) ≤ ENNReal.ofReal R := by
  obtain ⟨R, hR, hbound⟩ :=
    G.exists_pos_eventually_image_subset_ballAt hzero hzero hcomplete hK
  refine ⟨R, hR, ?_⟩
  filter_upwards [hbound,
    G.subsequence_strictMono.tendsto_atTop.eventually hmetric,
    G.subsequence_strictMono.tendsto_atTop.eventually htime,
    G.subsequence_strictMono.tendsto_atTop.eventually hRic] with k hk hm ht hRic
  intro x hx
  have hsource := hk (mem_image_of_mem (fun y => ((G.embedding k).toFun (0, y)).2) hx)
  change ((S.flow (G.subsequence k)).metricAt 0).edist
    (S.flow (G.subsequence k)).base (((G.embedding k).toFun (0, x)).2) <
      ENNReal.ofReal R at hsource
  rw [RiemannianMetric.edist_diffeomorph _ _ (e (G.subsequence k)) hm] at hsource
  exact ((F (G.subsequence k)).ball_subset_ball_of_ricci_nonneg ht
    (e (G.subsequence k) (S.flow (G.subsequence k)).base) R
    ⟨le_rfl, hst⟩ ⟨hst, le_rfl⟩ hst
    (fun u hu y _ v => hRic u hu y v) hsource).le

end PoincareConjecture.PointedGeometricConvergence
