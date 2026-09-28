import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedCompactImages
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

theorem eventually_generalized_terminal_baseBall_preimage_ball
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {A : ℝ} (hA : 0 < A) :
    ∀ᶠ k in atTop,
      (G.limit.flow.metric 0).ball G.limit.base (2 * A) ⊆ G.exhaustion.space k ∧
      ∀ x ∈ S.baseBall (G.subsequence k) A,
        ∃ y ∈ (G.limit.flow.metric 0).ball G.limit.base (2 * A),
          ∀ h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0,
            (G.embedding k).pointMap 0 h0 y =
              (⟨(S.base (G.subsequence k)).1, x⟩ :
                (S.flow (G.subsequence k)).point) := by
  let g := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  let K := closure (g.ball G.limit.base (4 * A))
  have hK : IsCompact K := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete
        (G.limit.complete 0 G.limit.zero_mem) G.limit.base (4 * A)) isClosed_closure
    apply closure_minimal
      (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal (4 * A)) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsmall : g.ball G.limit.base (2 * A) ⊆ K := by
    intro x hx
    exact subset_closure (hx.trans_le (ENNReal.ofReal_le_ofReal (by linarith)))
  have h0 (k : ℕ) : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have htransport (n : ℕ) (b : ℝ) (hb : b = (S.base n).1)
      (z : ((S.flow n).slice b).carrier)
      (hz : (⟨b, z⟩ : (S.flow n).point) = S.base n)
      (x : ((S.flow n).slice (S.base n).1).carrier) (hx : x ∈ S.baseBall n A) :
      ∃ w : ((S.flow n).slice b).carrier,
        w ∈ RiemannianMetric.ball
          (M13.scaleSmoothMetric ((S.flow n).metric b)
            (S.scale n) (S.base_scalar_pos n)) z A ∧
          (⟨b, w⟩ : (S.flow n).point) = ⟨(S.base n).1, x⟩ := by
    subst b
    have hz' : z = (S.base n).2 := eq_of_heq (Sigma.mk.inj_iff.mp hz).2
    refine ⟨x, ?_, rfl⟩
    rw [hz', scaled_terminal_ball_eq_baseBall]
    exact hx
  filter_upwards [eventually_generalized_tangent_comparison G G.limit.zero_mem
    0 (fun k => h0 (k + 0)) hK (by norm_num : (1 : ℝ) < 2)] with k hk
  let e := generalizedSliceHomeomorph G k 0 (h0 k)
  let h := normalizedBlowupSliceMetric S (G.subsequence k) 0
  have he : e.MDifferentiable (𝓡 3) (𝓡 3) := by
    constructor
    · intro x hx
      exact ((generalizedSliceHomeomorph_contMDiffAt G k 0 (h0 k) hx).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
    · intro y hy
      exact ((generalizedSliceHomeomorph_symm_contMDiffAt G k 0 (h0 k) hy).mdifferentiableAt
        (by simp)).mdifferentiableWithinAt
  have hinverse := g.inverse_tangentNorm_le_of_le h e he hk.1
    (fun x hx v => (hk.2 x hx v).2)
  have hcapture : h.ball (e G.limit.base) A ⊆ e '' g.ball G.limit.base (2 * A) :=
    g.ball_subset_image_ball_of_inverse_tangentNorm_le h e G.limit.base
      (by positivity : 0 < 4 * A) (by norm_num : (0 : ℝ) < 2) (by linarith)
      hK hk.1
      (fun y hy => (generalizedSliceHomeomorph_symm_contMDiffAt G k 0 (h0 k) hy).of_le
        (by simp)) hinverse
  refine ⟨hsmall.trans hk.1, ?_⟩
  intro x hx
  obtain ⟨w, hw, hwx⟩ := htransport (G.subsequence k)
    ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k)) (by simp)
    (e G.limit.base) (G.base_preserving k (h0 k)) x hx
  obtain ⟨y, hy, hyw⟩ := hcapture hw
  refine ⟨y, hy, ?_⟩
  intro hzero
  change (⟨(S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k), e y⟩ :
    (S.flow (G.subsequence k)).point) = _
  rw [hyw]
  exact hwx

end PoincareConjecture.M30
