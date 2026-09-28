import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SourceBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.SourceMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.PointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_image_ballAt_subset_ballAt
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t r C : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    (hC : 1 < C) :
    ∀ᶠ k : ℕ in atTop,
      (fun x => ((G.embedding k).toFun (t, x)).2) '' G.limitFlow.ballAt t r ⊆
        (S.flow (G.subsequence k)).ballAt t (C * r) := by
  let g := G.limitFlow.metricAt t
  have hcompact : IsCompact (closure (g.ball G.limitFlow.base r)) :=
    g.isCompact_closure_ball_of_metricComplete hcomplete G.limitFlow.base r
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_pullback_tangentNorm_bounds hcompact ht hC,
    eventually_ge_atTop j] with k hk hjk
  let h := (S.flow (G.subsequence k)).metricAt t
  let e := (G.embedding k).spatialHomeomorph (G.exhaustion_open k) ht
  have hsource : g.ball G.limitFlow.base r ⊆ e.source :=
    subset_closure.trans (hj.trans (G.exhaustion_monotone hjk))
  have he : ∀ x ∈ e.source, ContMDiffAt (𝓡 n) (𝓡 n) 1 e x :=
    fun x hx => ((G.embedding k).spatialMap_contMDiffAt
      (G.exhaustion_open k) ht hx).of_le (by simp)
  have hbound : ∀ x ∈ g.ball G.limitFlow.base r, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v :=
    fun x hx v => (hk x (subset_closure hx) v).1
  have hbase : e G.limitFlow.base = (S.flow (G.subsequence k)).base :=
    congrArg Prod.snd (G.base_preserving_at_time hT k ht)
  have himage := g.image_ball_subset_ball_of_tangentNorm_le h e G.limitFlow.base
    (zero_lt_one.trans hC) hsource he hbound
  rw [hbase] at himage
  exact himage

theorem exists_pos_eventually_image_subset_ballAt
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    {t : ℝ} (ht : t ∈ Ioo T' T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt t))
    {K : Set G.limitCarrier.carrier} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k : ℕ in atTop,
      (fun x => ((G.embedding k).toFun (t, x)).2) '' K ⊆
        (S.flow (G.subsequence k)).ballAt t R := by
  let g := G.limitFlow.metricAt t
  let : MetricSpace G.limitCarrier.carrier := G.limitCarrier.metricSpaceOf g
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 G.limitFlow.base
  have hball : K ⊆ G.limitFlow.ballAt t r := by
    change K ⊆ G.limitCarrier.metricBall g G.limitFlow.base r
    simpa only [G.limitCarrier.metricBall_eq_metricBallOf g] using hKr
  refine ⟨2 * r, mul_pos (by norm_num) hr, ?_⟩
  filter_upwards [G.eventually_image_ballAt_subset_ballAt hT ht hcomplete
    (r := r) (C := 2) (by norm_num)] with k hk
  exact (image_mono hball).trans hk

end PoincareConjecture.PointedGeometricConvergence
