import PoincareConjecture.Proofs.M30.Thm11_8.GeneralizedMetricComparison
import PoincareConjecture.Proofs.M30.Generalized.TerminalMetric
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.SourceMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

theorem exists_eventually_generalized_terminal_image_baseBall
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) :
    ∃ R : ℝ, 0 < R ∧ ∀ᶠ k in atTop,
      ∀ x ∈ K, ∃ y : ((S.flow (G.subsequence k)).slice
          (S.base (G.subsequence k)).1).carrier,
        y ∈ S.baseBall (G.subsequence k) R ∧
        ∀ h0 : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0,
          (G.embedding k).pointMap 0 h0 x =
            (⟨(S.base (G.subsequence k)).1, y⟩ : (S.flow (G.subsequence k)).point) := by
  let g := G.limit.flow.metric 0
  let : MetricSpace G.limit.carrier.carrier := G.limit.carrier.metricSpaceOf g
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_ball_lt 0 G.limit.base
  have hKr' : K ⊆ g.ball G.limit.base r := by
    simpa only [FlowCarrier.metricBall_eq_metricBallOf, FlowCarrier.metricBall] using hKr
  have hcompact : IsCompact (closure (g.ball G.limit.base r)) := by
    apply IsCompact.of_isClosed_subset
      (g.isCompact_closedBall_of_metricComplete
        (G.limit.complete 0 G.limit.zero_mem) G.limit.base r) isClosed_closure
    apply closure_minimal
      (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal r) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have h0 (k : ℕ) : (0 : ℝ) ∈ Icc (-G.exhaustion.time k) 0 :=
    ⟨neg_nonpos.mpr (G.exhaustion.time_pos k).le, le_rfl⟩
  have htransport (k : ℕ) (b : ℝ) (hb : b = (S.base k).1)
      (z x : ((S.flow k).slice b).carrier)
      (hz : (⟨b, z⟩ : (S.flow k).point) = S.base k)
      (hx : x ∈ RiemannianMetric.ball
        (M13.scaleSmoothMetric ((S.flow k).metric b)
          (S.scale k) (S.base_scalar_pos k)) z (2 * r)) :
      ∃ y : ((S.flow k).slice (S.base k).1).carrier,
        y ∈ S.baseBall k (2 * r) ∧
          (⟨b, x⟩ : (S.flow k).point) = ⟨(S.base k).1, y⟩ := by
    subst b
    have hz' : z = (S.base k).2 := eq_of_heq (Sigma.mk.inj_iff.mp hz).2
    refine ⟨x, ?_, rfl⟩
    rw [← scaled_terminal_ball_eq_baseBall]
    simpa only [hz'] using hx
  refine ⟨2 * r, by positivity, ?_⟩
  filter_upwards [eventually_generalized_tangent_comparison G G.limit.zero_mem
    0 (fun k => h0 (k + 0)) hcompact (by norm_num : (1 : ℝ) < 2)] with k hk
  let e := generalizedSliceHomeomorph G k 0 (h0 k)
  let h := normalizedBlowupSliceMetric S (G.subsequence k) 0
  have hsource : g.ball G.limit.base r ⊆ e.source := subset_closure.trans hk.1
  have himage := g.image_ball_subset_ball_of_tangentNorm_le h e G.limit.base
    (by norm_num : (0 : ℝ) < 2) hsource
    (fun x hx => (generalizedSliceHomeomorph_contMDiffAt G k 0 (h0 k) hx).of_le
      (by simp))
    (fun x hx v => (hk.2 x (subset_closure hx) v).1)
  intro x hx
  obtain ⟨y, hy, hxy⟩ := htransport (G.subsequence k)
    ((S.base (G.subsequence k)).1 + 0 / S.scale (G.subsequence k)) (by simp)
    (e G.limit.base) (e x) (G.base_preserving k (h0 k))
    (himage (mem_image_of_mem e (hKr' hx)))
  exact ⟨y, hy, fun _ => hxy⟩

end PoincareConjecture.M30
