import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.DimensionOne
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.CompleteBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 1)) M] [IsManifold (𝓡 1) ∞ M]

lemma isInvertible_mfderiv_of_euclidean_pullback_one (g : RiemannianMetric 1 M)
    {e : EuclideanSpace ℝ (Fin 1) → M} {x : EuclideanSpace ℝ (Fin 1)}
    (hmetric : ∀ v w : EuclideanSpace ℝ (Fin 1),
      g.pullbackCoefficients e x v w = inner ℝ v w) :
    (mfderiv (𝓡 1) (𝓡 1) e x).IsInvertible := by
  let A : EuclideanSpace ℝ (Fin 1) →L[ℝ] EuclideanSpace ℝ (Fin 1) :=
    mfderiv (𝓡 1) (𝓡 1) e x
  have hinj : Function.Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have h := hmetric v v
    change g.inner (e x) (A v) (A v) = inner ℝ v v at h
    rw [hv, map_zero] at h
    exact inner_self_eq_zero.mp h.symm
  have hsurj : Function.Surjective A :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hinj
  exact ⟨ContinuousLinearEquiv.ofBijective A (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr hsurj), rfl⟩

lemma pullbackCoefficients_eq_of_radial_norm_one (g : RiemannianMetric 1 M)
    {e : EuclideanSpace ℝ (Fin 1) → M} {U : Set (EuclideanSpace ℝ (Fin 1))}
    (hU : IsOpen U) (hzero : (0 : EuclideanSpace ℝ (Fin 1)) ∈ U)
    (he : ContMDiffOn (𝓡 1) (𝓡 1) ∞ e U)
    (hrad : ∀ x ∈ U,
      g.tangentNorm (e x) (mfderiv (𝓡 1) (𝓡 1) e x x) = ‖x‖)
    {x : EuclideanSpace ℝ (Fin 1)} (hx : x ∈ U)
    (v w : EuclideanSpace ℝ (Fin 1)) :
    g.pullbackCoefficients e x v w = inner ℝ v w := by
  have hdiag (z : EuclideanSpace ℝ (Fin 1)) (hz : z ∈ U) :
      g.pullbackCoefficients e z z z = inner ℝ z z := by
    have hnonneg : 0 ≤ g.inner (e z) (mfderiv (𝓡 1) (𝓡 1) e z z)
        (mfderiv (𝓡 1) (𝓡 1) e z z) := by
      by_cases hv : mfderiv (𝓡 1) (𝓡 1) e z z = 0
      · simp only [hv, map_zero]
        exact le_rfl
      · exact (g.pos _ _ hv).le
    have hsquare := congrArg (fun a : ℝ => a ^ 2) (hrad z hz)
    simpa only [tangentNorm, pullbackCoefficients, ContinuousLinearMap.bilinearComp_apply,
      Real.sq_sqrt hnonneg, real_inner_self_eq_norm_sq]
      using! hsquare
  have hnonzero (z : EuclideanSpace ℝ (Fin 1)) (hz : z ∈ U) (hne : z ≠ 0) :
      g.pullbackCoefficients e z v w = inner ℝ v w := by
    obtain ⟨a, rfl⟩ := exists_smul_eq_of_finrank_eq_one
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1) hne v
    obtain ⟨b, rfl⟩ := exists_smul_eq_of_finrank_eq_one
      (by simp : Module.finrank ℝ (EuclideanSpace ℝ (Fin 1)) = 1) hne w
    simp only [map_smul, smul_apply, smul_eq_mul, inner_smul_left, inner_smul_right,
      conj_trivial, hdiag z hz]
  by_cases hne : x ≠ 0
  · exact hnonzero x hx hne
  · have hxzero : x = 0 := not_ne_iff.mp hne
    subst x
    have hcoeff := (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (hU.mem_nhds hzero))).continuousAt
    have hc : ContinuousAt (fun z ↦ g.pullbackCoefficients e z v w) 0 :=
      (hcoeff.clm_apply continuousAt_const).clm_apply continuousAt_const
    have hnebot : (𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1))).NeBot :=
      Module.punctured_nhds_neBot ℝ (EuclideanSpace ℝ (Fin 1)) 0
    exact tendsto_nhds_unique_of_eventuallyEq
      (l := 𝓝[≠] (0 : EuclideanSpace ℝ (Fin 1)))
      (hc.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds (x := inner ℝ v w)) (by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hzero)] with z hzne hz
        exact hnonzero z hz hzne)

theorem exists_arclength_lift_of_precompact_ball_one [T2Space M]
    (g : RiemannianMetric 1 M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    ∃ e : EuclideanSpace ℝ (Fin 1) → M,
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v w : EuclideanSpace ℝ (Fin 1),
        g.pullbackCoefficients e x v w = inner ℝ v w) ∧
      ∀ x ∈ Metric.ball 0 R, g.edist p (e x) ≤ ENNReal.ofReal ‖x‖ := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p hR hcompact
  have hrad (x : EuclideanSpace ℝ (Fin 1)) (hx : x ∈ Metric.ball 0 R) :
      g.tangentNorm (e x) (mfderiv (𝓡 1) (𝓡 1) e x x) = ‖x‖ := by
    have hline : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have hem : MDifferentiableAt (𝓡 1) (𝓡 1) e ((1 : ℝ) • x) := by
      simpa only [one_smul] using
        (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp)
    have hd := mfderiv_comp (1 : ℝ) hem hline.differentiableAt.mdifferentiableAt
    rw [mfderiv_eq_fderiv] at hd
    have hd1 := congrArg (fun A => A (1 : ℝ)) hd
    change mfderiv 𝓘(ℝ, ℝ) (𝓡 1) (fun t : ℝ => e (t • x)) 1 1 =
      mfderiv (𝓡 1) (𝓡 1) e ((1 : ℝ) • x)
        (fderiv ℝ (fun t : ℝ => t • x) 1 1) at hd1
    simp only [TangentSpace] at hd1
    rw [fderiv_eq_smul_deriv, one_smul, hline.deriv, one_smul] at hd1
    have hspeed := ((hgeo x hx).2 1 (by simp)).1
    unfold tangentNorm at hspeed ⊢
    simp only [TangentSpace] at hspeed ⊢
    rw [one_smul, hd1] at hspeed
    exact hspeed
  refine ⟨e, he, he0, ?_, ?_⟩
  · intro x hx v w
    exact g.pullbackCoefficients_eq_of_radial_norm_one Metric.isOpen_ball
      (Metric.mem_ball_self hR) he hrad hx v w
  · intro x hx
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hgeo x hx).2 1 (by simp)).2

theorem exists_arclength_lift_of_metricComplete_one [T3Space M]
    (g : RiemannianMetric 1 M) (hcomplete : MetricComplete g)
    (p : M) {R : ℝ} (hR : 0 < R) :
    ∃ e : EuclideanSpace ℝ (Fin 1) → M,
      ContMDiffOn (𝓡 1) (𝓡 1) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v w : EuclideanSpace ℝ (Fin 1),
        g.pullbackCoefficients e x v w = inner ℝ v w) ∧
      ∀ x ∈ Metric.ball 0 R, g.edist p (e x) ≤ ENNReal.ofReal ‖x‖ := by
  have hcompact := g.isCompact_closedBall_of_metricComplete hcomplete p R
  apply g.exists_arclength_lift_of_precompact_ball_one p hR
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hcompact.isClosed
  exact fun q hq => (show g.edist p q < ENNReal.ofReal R from hq).le

end PoincareConjecture.RiemannianMetric
