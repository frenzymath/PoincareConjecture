import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialScalar
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialCurve
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactGauss
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalRadius













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture




theorem m64Intrinsic_exists_precompact_ball (N : IntrinsicAnnulus)
    (p : AnnulusCoordinates) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (closure (N.metric.ball p R)) := by
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨N.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle AnnulusCoordinates
      (TangentSpace (𝓡 2) : AnnulusCoordinates → Type _) :=
    ⟨⟨N.metric.inner, N.metric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  obtain ⟨r, hr, hsub⟩ := setOfPred_riemannianEDist_lt_subset_nhds (𝓡 2)
    (Metric.ball_mem_nhds p (by norm_num : (0 : ℝ) < 1))
  refine ⟨r, by exact_mod_cast hr, ?_⟩
  apply (isCompact_closedBall p (1 : ℝ)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro q hq
  apply Metric.ball_subset_closedBall
  apply hsub
  simpa only [RiemannianMetric.ball, mem_ofPred_eq, RiemannianMetric.edist,
    ENNReal.ofReal_coe_nnreal] using hq

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace





theorem m64Intrinsic_exists_regular_radial_exponential
    (N : IntrinsicAnnulus) (p : AnnulusCoordinates) :
    ∃ r : ℝ, 0 < r ∧ ∃ e : AnnulusCoordinates → AnnulusCoordinates,
      e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 r) ∧
      (∀ u v : AnnulusCoordinates,
        N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
          (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v) ∧
      (∀ v ∈ Metric.ball 0 r, ∀ w : AnnulusCoordinates,
        N.metric.inner (e v) (mfderiv (𝓡 2) (𝓡 2) e v v)
          (mfderiv (𝓡 2) (𝓡 2) e v w) = inner ℝ v w) ∧
      (∀ v ∈ Metric.ball 0 r,
        N.metric.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 r}) ∧
      (∀ v ∈ Metric.ball 0 r,
        Function.Injective (mfderiv (𝓡 2) (𝓡 2) e v)) ∧
      ∀ v ∈ Metric.ball 0 r,
        N.metric.edist p (e v) ≤ ENNReal.ofReal ‖v‖ := by
  obtain ⟨R, hR, hcompact⟩ := m64Intrinsic_exists_precompact_ball N p
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    N.metric.exists_orthonormal_radial_exponential_of_precompact_ball p hR hcompact
  have h0 : (0 : AnnulusCoordinates) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  have hezero := he.contMDiffAt (Metric.isOpen_ball.mem_nhds h0)
  have hmetric : ∀ u v : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 u)
        (mfderiv (𝓡 2) (𝓡 2) e 0 v) = inner ℝ u v := by
    intro u v
    exact N.metric.pullbackCoefficients_zero_of_orthonormal p hezero he0 hed hL u v
  have hinj : Function.Injective (fderiv ℝ e 0) := by
    intro u v huv
    have h := hmetric (u - v) (u - v)
    simp only [TangentSpace, mfderiv_eq_fderiv] at h
    change N.metric.inner (e 0) ((fderiv ℝ e 0) (u - v))
      ((fderiv ℝ e 0) (u - v)) = inner ℝ (u - v) (u - v) at h
    rw [map_sub, huv, sub_self, map_zero] at h
    exact sub_eq_zero.mp ((inner_self_eq_zero (𝕜 := ℝ)
      (E := AnnulusCoordinates)).mp h.symm)
  let A : AnnulusCoordinates ≃L[ℝ] AnnulusCoordinates :=
    (LinearEquiv.ofBijective (fderiv ℝ e 0).toLinearMap
      ⟨hinj, (LinearMap.injective_iff_surjective (f := (fderiv ℝ e 0).toLinearMap)).mp
        hinj⟩).toContinuousLinearEquiv
  have hA : A.toContinuousLinearMap = fderiv ℝ e 0 := rfl
  have hfd : ContinuousAt (fderiv ℝ e) 0 :=
    ((contMDiffAt_iff_contDiffAt.mp hezero).fderiv_right (m := 0) (by simp)).continuousAt
  have hinvertible : {v : AnnulusCoordinates | (fderiv ℝ e v).IsInvertible} ∈ 𝓝 0 := by
    have h := A.nhds
    rw [hA] at h
    exact hfd.preimage_mem_nhds h
  obtain ⟨r, hr, hsmall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (Metric.isOpen_ball.mem_nhds h0) hinvertible)
  have hball : Metric.ball (0 : AnnulusCoordinates) r ⊆ Metric.ball 0 R :=
    fun v hv => (hsmall hv).1
  refine ⟨r, hr, e, he0, he.mono hball, hmetric, ?_, ?_, ?_, ?_⟩
  · intro v hv w
    exact CoordinateExponential.gauss_identity_of_radial_family N.metric he
      (fun z hz => (hgeo z hz).1)
      (fun z hz t ht => ((hgeo z hz).2 t ht).1) v (hball hv) w
  · intro v hv t ht
    exact (hgeo v (hball hv)).1 t (hball ht)
  · intro v hv
    rw [mfderiv_eq_fderiv]
    exact (hsmall hv).2.injective
  · intro v hv
    simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
      ((hgeo v (hball hv)).2 1 (by simp)).2

end PoincareConjecture
