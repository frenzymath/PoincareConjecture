import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Hessian.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.EndpointBall

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.RiemannianMetric.Hessian

open ConnectionVariation ConnectionAlongCurve CoordinateExponential Toponogov

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1200000 in

theorem radial_pairing_le_sub_endpoint_ball_curvature [T2Space M]
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
    {κ ρ : ℝ} (hρ : 0 ≤ ρ) (hρv : ρ ≤ ‖v‖)
    (hball : ∀ y, (g.edist y (e v)).toReal ≤ ρ → ∀ u z,
      κ * (g.inner y u u * g.inner y z z - (g.inner y u z) ^ 2) ≤
        D.curvatureTensor y u z u z)
    (w : EuclideanSpace ℝ (Fin n)) :
    g.pullbackCoefficients e v
        (w + coordinateChristoffel (g.pullbackCoefficients e) v v w) w ≤
      g.pullbackCoefficients e v w w -
        κ * (‖v‖ ^ 2 * g.pullbackCoefficients e v w w - (inner ℝ v w) ^ 2) *
          ((1 - (1 - ρ / ‖v‖) ^ 3) / 3) := by
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
  have hbound := Conjugate.jacobi_inner_le_sub_endpoint_ball_curvature D
    (by linarith : -a / 2 < 0) (by linarith : 1 < (a + 1) / 2) hρ hρv
    isOpen_Ioo hqgeo hsub hJ hjac
    (radialVariation_field_zero e v w) (norm_pos_iff.mpr hv0) hspeed
    (by simpa only [q, zero_smul, one_smul] using hmin) hsec
    (by simpa only [q, one_smul] using hball)
  rw [radialVariation_endpoint_pairing_eq g he hv hi w] at hbound
  have hev := (he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp)
  have hfield : J 1 = mfderiv (𝓡 n) (𝓡 n) e v w :=
    radialVariation_field_one v w hev
  have hvelocity : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1 =
      mfderiv (𝓡 n) (𝓡 n) e v v := by
    have hvel := radial_velocity_eq_differential (e := e) v (t := 1)
      (by simpa only [one_smul] using hev)
    rw [show (1 : ℝ) • v = v from one_smul ℝ v] at hvel
    exact hvel
  have hnormJ : g.tangentNorm (q 1) (J 1) ^ 2 = g.inner (q 1) (J 1) (J 1) := by
    apply Real.sq_sqrt
    by_cases hz : J 1 = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  have hpair : g.inner (q 1) (J 1) (J 1) = g.pullbackCoefficients e v w w := by
    rw [hfield]
    exact congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner (e z)
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w)
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w))
        (one_smul ℝ v)
  have hradialPair : g.inner (q 1) (J 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 1 1) =
      inner ℝ v w := by
    rw [hfield, hvelocity]
    change g.inner (e ((1 : ℝ) • v)) (mfderiv (𝓡 n) (𝓡 n) e v w)
      (mfderiv (𝓡 n) (𝓡 n) e v v) = inner ℝ v w
    rw [one_smul, g.symm]
    exact g.radial_gauss_identity D he hnorm hradial v hv w
  rw [hnormJ, hpair, hradialPair] at hbound
  exact hbound

end PoincareConjecture.RiemannianMetric.Hessian
