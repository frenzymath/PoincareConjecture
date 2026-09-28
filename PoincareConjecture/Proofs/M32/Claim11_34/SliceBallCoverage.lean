import PoincareConjecture.Proofs.M32.Claim11_34.SliceEmbedding
import PoincareConjecture.Proofs.M32.Claim11_34.SliceCurvatureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.Coverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space

private theorem sqrt_le_twice_of_half_error {a b : ℝ}
    (h : |b - a| ≤ (1 / 2 : ℝ) * a) : Real.sqrt a ≤ 2 * Real.sqrt b := by
  have ha : 0 ≤ a := by nlinarith [abs_nonneg (b - a)]
  have hb : 0 ≤ b := by linarith [(abs_le.mp h).1]
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity, ?_⟩
  rw [mul_pow, Real.sq_sqrt hb]
  nlinarith [(abs_le.mp h).1]




theorem blowup_eventually_slice_inverse_balls
    {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence S J) {t : ℝ} (ht : t ∈ J)
    {K : Set G.limit.carrier.carrier} (hK : IsCompact K)
    {r : ℝ} (hr : 0 < r) :
    ∃ Kplus : Set G.limit.carrier.carrier, IsCompact Kplus ∧ K ⊆ Kplus ∧
      ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
        Kplus ⊆ (blowup_sliceEmbedding G k t htk).source ∧
        ∀ x ∈ K,
          (rescaledMetric ((S.flow (G.subsequence k)).metric
            ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
            (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))).ball
              (blowup_sliceEmbedding G k t htk x) r ⊆
            blowup_sliceEmbedding G k t htk '' (G.limit.flow.metric t).ball x (2 * r) ∧
          ∀ y ∈ (rescaledMetric ((S.flow (G.subsequence k)).metric
            ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
            (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))).ball
              (blowup_sliceEmbedding G k t htk x) r,
            y ∈ (blowup_sliceEmbedding G k t htk).target ∧
              (blowup_sliceEmbedding G k t htk).symm y ∈ Kplus := by
  let g := G.limit.flow.metric t
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : MetricSpace G.limit.carrier.carrier := g.toMetricSpace
  let : ProperSpace G.limit.carrier.carrier := g.properSpace_toMetricSpace (G.limit.complete t ht)
  obtain ⟨A, hA, hKA⟩ := hK.isBounded.subset_ball_lt 0 G.limit.base
  let R := 2 * r + 1
  have hR : 0 < R := by dsimp [R]; positivity
  let Kplus := Metric.closedBall G.limit.base (A + R)
  have hplus : IsCompact Kplus := isCompact_closedBall _ _
  have hKK : K ⊆ Kplus := by
    apply hKA.trans
    exact Metric.ball_subset_closedBall.trans
      (Metric.closedBall_subset_closedBall (by linarith))
  have hclosure (x : G.limit.carrier.carrier) (hx : x ∈ K) :
      closure (g.ball x R) ⊆ Kplus := by
    rw [← g.toMetricSpace_ball]
    intro y hy
    have hyd : dist y x ≤ R :=
      closure_minimal Metric.ball_subset_closedBall Metric.isClosed_closedBall hy
    have hxd : dist x G.limit.base < A := hKA hx
    change dist y G.limit.base ≤ A + R
    exact (dist_triangle y x G.limit.base).trans (by linarith)
  have hsmall (x : G.limit.carrier.carrier) :
      g.ball x (2 * r) ⊆ closure (g.ball x R) := by
    rw [← g.toMetricSpace_ball, ← g.toMetricSpace_ball]
    exact (Metric.ball_subset_ball (by dsimp [R]; linarith)).trans subset_closure
  refine ⟨Kplus, hplus, hKK, ?_⟩
  filter_upwards [blowup_eventually_sliceMetric_error G ht hplus
    (by norm_num : (0 : ℝ) < 1 / 2)] with k hk
  obtain ⟨htk, hsource, herror⟩ := hk
  let e := blowup_sliceEmbedding G k t htk
  let h := rescaledMetric ((S.flow (G.subsequence k)).metric
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)))
    (S.scale (G.subsequence k)) (S.base_scalar_pos (G.subsequence k))
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source :=
    (blowup_sliceEmbedding_smooth G k t htk).1
  have hei : ∀ y ∈ e.target, ContMDiffAt (𝓡 3) (𝓡 3) ∞ e.symm y :=
    fun y hy => ((blowup_sliceEmbedding_smooth G k t htk).2 y hy).contMDiffAt
      (e.open_target.mem_nhds hy)
  have hediff : e.MDifferentiable (𝓡 3) (𝓡 3) :=
    ⟨he.mdifferentiableOn (by simp), fun y hy =>
      ((hei y hy).mdifferentiableAt (by simp)).mdifferentiableWithinAt⟩
  have hnorm (z : G.limit.carrier.carrier) (hz : z ∈ Kplus)
      (v : TangentSpace (𝓡 3) z) :
      g.tangentNorm z v ≤ 2 * h.tangentNorm (e z)
        (mfderiv (𝓡 3) (𝓡 3) e z v) := by
    apply sqrt_le_twice_of_half_error
    dsimp only [h]
    rw [rescaledMetric_inner]
    change |(G.embedding k).pullbackInner t htk z v v -
      (G.limit.flow.metric t).inner z v v| ≤ _
    exact herror z hz v
  refine ⟨htk, hsource, ?_⟩
  intro x hx
  have hballsource : closure (g.ball x R) ⊆ e.source := (hclosure x hx).trans hsource
  have hbound : ∀ y ∈ e '' closure (g.ball x R), ∀ v : TangentSpace (𝓡 3) y,
      g.tangentNorm (e.symm y) (mfderiv (𝓡 3) (𝓡 3) e.symm y v) ≤
        2 * h.tangentNorm y v := by
    rintro y ⟨z, hz, rfl⟩ v
    have hleft := e.left_inv (hballsource hz)
    have hback := congrArg (fun A => A v)
      (hediff.comp_symm_deriv (e.map_source (hballsource hz)))
    simp only [ContinuousLinearMap.comp_apply] at hback
    rw [hleft] at hback
    have hh := hnorm z (hclosure x hx hz) (mfderiv (𝓡 3) (𝓡 3) e.symm (e z) v)
    erw [hback] at hh
    erw [hleft]
    exact hh
  have hcover := g.ball_subset_image_ball_of_inverse_tangentNorm_le h e x
    (r := r) hR (by norm_num : (0 : ℝ) < 2) (by dsimp [R]; linarith)
    (hplus.of_isClosed_subset isClosed_closure (hclosure x hx)) hballsource
    (fun y hy => (hei y hy).of_le (by simp)) hbound
  refine ⟨hcover, ?_⟩
  intro y hy
  obtain ⟨z, hz, rfl⟩ := hcover hy
  have hzplus := hclosure x hx (hsmall x hz)
  refine ⟨e.map_source (hsource hzplus), ?_⟩
  rw [e.left_inv (hsource hzplus)]
  exact hzplus

end PoincareConjecture.M32
