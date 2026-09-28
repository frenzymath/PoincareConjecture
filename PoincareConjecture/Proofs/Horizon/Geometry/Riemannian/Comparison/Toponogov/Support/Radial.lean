import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.RadialHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialHessian
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Radial.Jacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.CoordinateExponential

private theorem hasDerivAt_radial_metric_self_pairing
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {v : E}
    (hB : DifferentiableAt ℝ B v) (hi : (B v).IsInvertible)
    (hsymm : ∀ᶠ x in 𝓝 v, ∀ a b, B x a b = B x b a) (w : E) :
    HasDerivAt (fun r : ℝ => B (r • v) (r • w) (r • w))
      (2 * B v (w + coordinateChristoffel B v v w) w) 1 := by
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace
  have hline (u : E) : HasDerivAt (fun r : ℝ => r • u) u 1 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (1 : ℝ)).smul_const u
  have hcoeff : HasDerivAt (fun r : ℝ => B (r • v)) (fderiv ℝ B v v) 1 :=
    hB.hasFDerivAt.comp_hasDerivAt_of_eq 1 (hline v) (one_smul ℝ v).symm
  have hd := (hcoeff.clm_apply (hline w)).clm_apply (hline w)
  apply hd.congr_deriv
  simp only [one_smul, add_apply]
  rw [fderiv_metric_eq_christoffel hB hi hsymm w w v]
  rw [hsymm.self_of_nhds w (coordinateChristoffel B v v w)]
  simp only [map_add, add_apply]
  ring

end PoincareConjecture.CoordinateExponential

namespace PoincareConjecture.RiemannianMetric.Toponogov

open ConnectionVariation ConnectionAlongCurve CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem radialVariation_endpoint_pairing_eq
    (g : RiemannianMetric n M)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hi : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v))
    (w : EuclideanSpace ℝ (Fin n)) :
    let q : ℝ → M := fun r => e (r • v)
    let J : (r : ℝ) → TangentSpace (𝓡 n) (q r) := fun r =>
      mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (r • (v + s • w))) 0 1
    g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) =
      g.pullbackCoefficients e v
        (w + coordinateChristoffel (g.pullbackCoefficients e) v v w) w := by
  let q : ℝ → M := fun r => e (r • v)
  let J : (r : ℝ) → TangentSpace (𝓡 n) (q r) := fun r =>
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (r • (v + s • w))) 0 1
  have hev := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)
  have hq : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ q 1 := by
    have hev' : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e ((1 : ℝ) • v) := by
      simpa only [one_smul] using hev
    exact hev'.comp 1 (contMDiffAt_iff_contDiffAt.mpr (by fun_prop))
  have hJ : ContDiffAt ℝ ∞ (chartField q (q 1) J) 1 :=
    contDiffAt_chartField_radialVariation_of_ball he v w (by simpa only [one_smul] using hv)
  have hmetric := hasDerivAt_metric_inner_along g hq hJ hJ
  have hcoord := hasDerivAt_radial_metric_self_pairing
    ((g.contDiffAt_pullbackCoefficients hev).differentiableAt (by simp))
    (g.isInvertible_pullbackCoefficients hi.1)
    (Eventually.of_forall fun _ a b => g.symm _ _ _) w
  have heq : (fun r => g.inner (q r) (J r) (J r)) =ᶠ[𝓝 (1 : ℝ)]
      (fun r : ℝ => g.pullbackCoefficients e (r • v) (r • w) (r • w)) := by
    have hnear : ∀ᶠ r in 𝓝 (1 : ℝ), r • v ∈ Metric.ball 0 R :=
      (show ContinuousAt (fun r : ℝ => r • v) 1 by fun_prop).preimage_mem_nhds
        (by simpa only [one_smul] using Metric.isOpen_ball.mem_nhds hv)
    filter_upwards [hnear] with r hr
    have hfield := radialVariation_field_eq v w r
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hr)).mdifferentiableAt (by simp))
    change g.inner (e (r • v)) (J r) (J r) = _
    rw [show J r = mfderiv (𝓡 n) (𝓡 n) e (r • v) (r • w) from hfield]
    rfl
  have hderiv := hmetric.unique (hcoord.congr_of_eventuallyEq heq)
  rw [g.symm (q 1) (J 1) (manifoldCovDerivAlong g q J 1 1)] at hderiv
  change g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) = _
  linarith

set_option maxHeartbeats 1200000 in



theorem radial_pairing_le_of_nonnegative_sectional [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v))
        {r : ℝ | r • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hv0 : v ≠ 0)
    (hi : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e v))
    (hmin : g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖)
    (w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients e v
        (w + coordinateChristoffel (g.pullbackCoefficients e) v v w) w ≤
      g.pullbackCoefficients e v w w := by
  obtain ⟨S, a, _, h0, ha, _, hdom⟩ := exists_radial_variation_rectangle hv w
  let q : ℝ → M := fun r => e (r • v)
  let J : (r : ℝ) → TangentSpace (𝓡 n) (q r) := fun r =>
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (r • (v + s • w))) 0 1
  have htime (r : ℝ) (hr : r ∈ Ioo (-a) a) : r • v ∈ Metric.ball 0 R := by
    simpa only [zero_smul, add_zero] using hdom 0 h0 r hr
  have hqgeo : g.IsGeodesicOn q (Ioo (-a) a) :=
    fun r hr => hradial v hv r (htime r hr)
  have hJ : ∀ r ∈ Ioo (-a) a, ContDiffAt ℝ ∞ (chartField q (q r) J) r :=
    fun r hr => contDiffAt_chartField_radialVariation_of_ball he v w (htime r hr)
  have hzero : (0 : ℝ) ∈ Ioo (-a) a := by constructor <;> linarith
  have hspeed0 :
      g.tangentNorm (q 0) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = ‖v‖ := by
    have hvel := radial_velocity_eq_differential v
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds (htime 0 hzero))).mdifferentiableAt
        (by simp))
    change g.tangentNorm (e ((0 : ℝ) • v))
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = ‖v‖
    rw [hvel]
    change Real.sqrt (g.pullbackCoefficients e ((0 : ℝ) • v) v v) = ‖v‖
    rw [zero_smul, hnorm, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg v)]
  have hspeed : ∀ r ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (q r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) = ‖v‖ := by
    intro r hr
    have ht : r ∈ Ioo (-a) a := by constructor <;> linarith [hr.1, hr.2]
    have hconst := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (-a) a).isPreconnected
      (fun s hs => (hqgeo.hasDerivAt_tangentNorm_zero hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hqgeo.hasDerivAt_tangentNorm_zero hs).deriv) ht hzero
    exact hconst.trans hspeed0
  have hjac : ∀ r ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g q (manifoldCovDerivAlong g q J 1) 1 r =
        -D.curvature (q r) (J r) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q r 1) := by
    intro r hr
    exact eq_neg_of_add_eq_zero_left (g.radialVariation_jacobi D he hradial hv w hr)
  have hsub : Icc (-a / 2) ((a + 1) / 2) ⊆ Ioo (-a) a := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hbound := Conjugate.jacobi_inner_le_of_minimizing D
    (by linarith : -a / 2 < 0) (by linarith : 1 < (a + 1) / 2)
    isOpen_Ioo hqgeo hsub hJ hjac
    (radialVariation_field_zero e v w) (norm_pos_iff.mpr hv0) hspeed
    (by simpa only [q, zero_smul, one_smul] using hmin) hsec
  change g.inner (q 1) (manifoldCovDerivAlong g q J 1 1) (J 1) ≤
    g.inner (q 1) (J 1) (J 1) at hbound
  rw [radialVariation_endpoint_pairing_eq g he hv hi w] at hbound
  have hfield := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hfield
  rw [hfield] at hbound
  have hpair := congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner (e z)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w))
      (one_smul ℝ v)
  exact hbound.trans_eq hpair




theorem deriv2_norm_sq_le_of_minimizing_radial [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : D.NonnegativeSectionalCurvature)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v))
        {r : ℝ | r • v ∈ Metric.ball 0 R})
    {u : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hut : u t ∈ Metric.ball 0 R) (hut0 : u t ≠ 0)
    (hi : Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e (u t)))
    (hmin : g.edist (e 0) (e (u t)) = ENNReal.ofReal ‖u t‖)
    (hu : ContDiffAt ℝ 2 u t)
    (hgeo : deriv (deriv u) t =
      -coordinateChristoffel (g.pullbackCoefficients e) (u t) (deriv u t) (deriv u t)) :
    (deriv^[2] (fun s => ‖u s‖ ^ 2)) t ≤
      2 * g.pullbackCoefficients e (u t) (deriv u t) (deriv u t) := by
  rw [g.deriv2_norm_sq_eq_precompact_radial_pairing D he hnorm hradial hut hi hu hgeo]
  exact mul_le_mul_of_nonneg_left
    (radial_pairing_le_of_nonnegative_sectional g D hsec he hnorm hradial hut hut0 hi
      hmin (deriv u t)) (by norm_num)

end PoincareConjecture.RiemannianMetric.Toponogov
