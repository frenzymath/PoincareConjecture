import PoincareConjecture.Proofs.M32.Claim11_34.InverseConfinement
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric













set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space




theorem blowup_eventually_zeroSliceEmbedding_image_ball
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {r C : ℝ} (_hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      (G.limit.flow.metric 0).ball G.limit.base r ⊆
        (blowup_zeroSliceEmbedding G k).source ∧
      blowup_zeroSliceEmbedding G k '' (G.limit.flow.metric 0).ball G.limit.base r ⊆
        S.baseBall (G.subsequence k) (C * r) := by
  let g := G.limit.flow.metric 0
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier :=
    g.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  let K := Metric.closedBall G.limit.base (r + 1)
  have hcompact : IsCompact K := isCompact_closedBall _ _
  have hball : g.ball G.limit.base r ⊆ K := by
    rw [← g.toMetricSpace_ball]
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G hcompact
  filter_upwards [blowup_eventually_zero_tangentNorm_bounds G hcompact hC,
    eventually_ge_atTop j] with k hk hjk
  let e := blowup_zeroSliceEmbedding G k
  have hsource : K ⊆ e.source := by
    intro x hx
    change x ∈ (blowup_zeroSliceEmbedding G k).source
    rw [blowup_zeroSliceEmbedding_source]
    exact G.exhaustion.space_increasing hjk (hj hx)
  have hsmooth : ∀ x ∈ e.source, ContMDiffAt (𝓡 3) (𝓡 3) 1 e x := by
    intro x hx
    have h := blowup_zeroSliceEmbedding_smooth G k
    rw [← blowup_zeroSliceEmbedding_source] at h
    exact ((h x hx).contMDiffAt (e.open_source.mem_nhds hx)).of_le (by simp)
  refine ⟨hball.trans hsource, ?_⟩
  have himage := g.image_ball_subset_ball_of_tangentNorm_le
    (blowup_zeroSourceMetric G k) e G.limit.base (zero_lt_one.trans hC)
    (hball.trans hsource) hsmooth (fun x hx v => (hk x (hball hx) v).1)
  rintro y ⟨x, hx, rfl⟩
  have hm : e x ∈ (blowup_zeroSourceMetric G k).ball (e G.limit.base) (C * r) :=
    himage (mem_image_of_mem e hx)
  have hbase : e G.limit.base = (S.base (G.subsequence k)).2 :=
    blowup_zeroSliceEmbedding_base G k
  rw [hbase, blowup_zeroSourceMetric_ball] at hm
  exact hm

end PoincareConjecture.M32
