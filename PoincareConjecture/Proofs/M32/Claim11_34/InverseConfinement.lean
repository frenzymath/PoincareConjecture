import PoincareConjecture.Proofs.M32.Claim11_34.MetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

private theorem eventually_ball_confinement_package
    (G : GeneralizedBlowupConvergence S J) {r C : ℝ} (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop,
      (G.limit.flow.metric 0).ball G.limit.base (C * r) ⊆
        (blowup_zeroSliceEmbedding G k).source ∧
      S.baseBall (G.subsequence k) r ⊆
        blowup_zeroSliceEmbedding G k ''
          (G.limit.flow.metric 0).ball G.limit.base (C * r) := by
  let g := G.limit.flow.metric 0
  let R := C * r + 1
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 3) : G.limit.carrier.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : G.limit.carrier.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace G.limit.carrier.carrier :=
    EMetricSpace.ofRiemannianMetric (𝓡 3) G.limit.carrier.carrier
  have hcompact : IsCompact (closure (g.ball G.limit.base R)) := by
    apply (g.isCompact_closedBall_of_metricComplete
      (G.limit.complete 0 G.limit.zero_mem) G.limit.base R).of_isClosed_subset
      isClosed_closure
    apply closure_minimal (fun x (hx : g.edist G.limit.base x < ENNReal.ofReal R) => hx.le)
    exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hsmall : g.ball G.limit.base (C * r) ⊆ closure (g.ball G.limit.base R) := by
    intro x hx
    apply subset_closure
    exact (show g.edist G.limit.base x < ENNReal.ofReal (C * r) from hx).trans_le
      (ENNReal.ofReal_le_ofReal (by dsimp [R]; linarith))
  obtain ⟨j, hj⟩ := blowup_exists_exhaustion_superset G hcompact
  filter_upwards [blowup_eventually_zero_tangentNorm_bounds G hcompact hC,
    eventually_ge_atTop j] with k hk hjk
  let e := blowup_zeroSliceEmbedding G k
  let h := blowup_zeroSourceMetric G k
  have hsource : closure (g.ball G.limit.base R) ⊆ e.source := by
    simpa only [e, blowup_zeroSliceEmbedding_source] using
      hj.trans (G.exhaustion.space_increasing hjk)
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := by
    simpa only [e, blowup_zeroSliceEmbedding_source] using blowup_zeroSliceEmbedding_smooth G k
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm y :=
    fun y hy => (blowup_zeroSliceEmbedding_symm_smooth G k y hy).contMDiffAt
      (e.open_target.mem_nhds hy)
  have hediff : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), fun y hy =>
      (hei y hy).mdifferentiableAt (by simp) |>.mdifferentiableWithinAt⟩
  have hbound : ∀ y ∈ e '' closure (g.ball G.limit.base R),
      ∀ v : TangentSpace (𝓡 3) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) ≤
        C * h.tangentNorm y v := by
    rintro y ⟨x, hx, rfl⟩ v
    have hleft := e.left_inv (hsource hx)
    have hback := congrArg (fun A => A v)
      (hediff.comp_symm_deriv (e.map_source (hsource hx)))
    simp only [ContinuousLinearMap.comp_apply] at hback
    rw [hleft] at hback
    have hh := (hk x hx (mfderiv (𝓡 3) (𝓡 3) e.symm (e x) v)).2
    change g.tangentNorm x _ ≤ C * h.tangentNorm (e x)
      (mfderiv (𝓡 3) (𝓡 3) e x _) at hh
    erw [hback] at hh
    erw [hleft]
    exact hh
  have hcover := g.ball_subset_image_ball_of_inverse_tangentNorm_le h e G.limit.base
    (r := r) hR hCpos (by dsimp [R]; linarith) hcompact hsource
    (fun y hy => (hei y hy).of_le (by simp)) hbound
  rw [blowup_zeroSliceEmbedding_base, blowup_zeroSourceMetric_ball] at hcover
  exact ⟨hsmall.trans hsource, hcover⟩

theorem blowup_eventually_baseBall_subset_zeroSliceEmbedding_image_ball
    (G : GeneralizedBlowupConvergence S J) {r C : ℝ} (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop, S.baseBall (G.subsequence k) r ⊆
      blowup_zeroSliceEmbedding G k ''
        (G.limit.flow.metric 0).ball G.limit.base (C * r) :=
  (eventually_ball_confinement_package G hr hC).mono fun _ hk => hk.2

theorem blowup_eventually_zeroSliceEmbedding_inverse_ball
    (G : GeneralizedBlowupConvergence S J) {r C : ℝ} (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ y ∈ S.baseBall (G.subsequence k) r,
      y ∈ (blowup_zeroSliceEmbedding G k).target ∧
      (blowup_zeroSliceEmbedding G k).symm y ∈
        (G.limit.flow.metric 0).ball G.limit.base (C * r) := by
  filter_upwards [eventually_ball_confinement_package G hr hC] with k hk y hy
  obtain ⟨x, hx, rfl⟩ := hk.2 hy
  refine ⟨(blowup_zeroSliceEmbedding G k).map_source (hk.1 hx), ?_⟩
  rw [(blowup_zeroSliceEmbedding G k).left_inv (hk.1 hx)]
  exact hx

end PoincareConjecture.M32
