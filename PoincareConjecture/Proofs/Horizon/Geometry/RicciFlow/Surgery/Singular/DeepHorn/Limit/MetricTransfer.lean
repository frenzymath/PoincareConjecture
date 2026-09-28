import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Limit.MetricConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.LimitTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedBlowupConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

variable {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}

noncomputable def zeroSourceMetric (G : GeneralizedBlowupConvergence S J) (k : ℕ) :
    RiemannianMetric 3
      ((S.flow (G.subsequence k)).slice (S.base (G.subsequence k)).1).carrier :=
  rescaledMetric ((S.flow (G.subsequence k)).metric (S.base (G.subsequence k)).1)
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))

theorem zeroSourceMetric_ball (G : GeneralizedBlowupConvergence S J) (k : ℕ) (r : ℝ) :
    (G.zeroSourceMetric k).ball (S.base (G.subsequence k)).2 r =
      S.baseBall (G.subsequence k) r := by
  rw [zeroSourceMetric, rescaledMetric_ball_allDimensions]
  rfl

theorem zeroPullbackForm_eq_sourceMetric (G : GeneralizedBlowupConvergence S J)
    (k : ℕ) (x : G.limit.carrier.carrier) (v w : TangentSpace (𝓡 3) x) :
    G.zeroPullbackForm k x v w =
      (G.zeroSourceMetric k).inner (G.zeroSliceEmbedding k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.zeroSliceEmbedding k) x v)
        (mfderiv (𝓡 3) (𝓡 3) (G.zeroSliceEmbedding k) x w) := by
  rw [zeroSourceMetric, rescaledMetric_inner]
  exact (G.embedding k).zeroSliceHomeomorph_pullbackInner
    (G.exhaustion.space_open k) (G.zero_mem_cylinder k) x v w

theorem eventually_zero_tangentNorm_bounds (G : GeneralizedBlowupConvergence S J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K) {C : ℝ} (hC : 1 < C) :
    ∀ᶠ k in atTop, ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
      (G.zeroSourceMetric k).tangentNorm (G.zeroSliceEmbedding k x)
        (mfderiv (𝓡 3) (𝓡 3) (G.zeroSliceEmbedding k) x v) ≤
        C * (G.limit.flow.metric 0).tangentNorm x v ∧
      (G.limit.flow.metric 0).tangentNorm x v ≤
        C * (G.zeroSourceMetric k).tangentNorm (G.zeroSliceEmbedding k x)
          (mfderiv (𝓡 3) (𝓡 3) (G.zeroSliceEmbedding k) x v) := by
  have hε : 0 < (C - 1) / C := div_pos (sub_pos.mpr hC) (zero_lt_one.trans hC)
  filter_upwards [G.eventually_zeroPullbackForm_error hK hε] with k hk x hx v
  apply (G.limit.flow.metric 0).tangentNorm_pullback_bounds_of_unit_error
    (G.zeroSourceMetric k) (G.zeroSliceEmbedding k) hC
  intro w hw
  have hwu : (G.limit.flow.metric 0).inner x w w ≤ 1 := Real.sqrt_le_one.mp hw
  rw [← G.zeroPullbackForm_eq_sourceMetric]
  exact (hk x hx w w hwu hwu).le

theorem eventually_baseBall_subset_zeroSliceEmbedding_image_ball
    (G : GeneralizedBlowupConvergence S J) {r C : ℝ} (hr : 0 < r) (hC : 1 < C) :
    ∀ᶠ k in atTop, S.baseBall (G.subsequence k) r ⊆
      G.zeroSliceEmbedding k '' (G.limit.flow.metric 0).ball G.limit.base (C * r) := by
  let g := G.limit.flow.metric 0
  let R := C * r + 1
  have hCpos : 0 < C := zero_lt_one.trans hC
  have hR : 0 < R := by dsimp [R]; positivity
  have hcompact : IsCompact (closure (g.ball G.limit.base R)) :=
    g.isCompact_closure_ball_of_metricComplete
      (G.limit.complete 0 G.limit.zero_mem) G.limit.base R
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset hcompact
  filter_upwards [G.eventually_zero_tangentNorm_bounds hcompact hC,
    eventually_ge_atTop j] with k hk hjk
  let e := G.zeroSliceEmbedding k
  let h := G.zeroSourceMetric k
  have hsource : closure (g.ball G.limit.base R) ⊆ e.source := by
    simpa only [e, G.zeroSliceEmbedding_source] using
      hj.trans (G.exhaustion.space_increasing hjk)
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source := by
    simpa only [e, G.zeroSliceEmbedding_source] using G.zeroSliceEmbedding_smooth k
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm y :=
    fun y hy => (G.zeroSliceEmbedding_symm_smooth k y hy).contMDiffAt
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
    have hback := congrArg (fun A => A v) (hediff.comp_symm_deriv (e.map_source (hsource hx)))
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
  rw [G.zeroSliceEmbedding_base, G.zeroSourceMetric_ball] at hcover
  exact hcover

end PoincareConjecture.GeneralizedBlowupConvergence
