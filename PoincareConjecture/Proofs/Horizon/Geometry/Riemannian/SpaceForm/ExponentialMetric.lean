import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.GeodesicJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.RadialGauss

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.SpaceForm

open ConnectionAlongCurve ConnectionVariation RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem normalExponential_inner_self
    (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
        (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v)
    (hsec : ∀ x ∈ U, ∀ u v : TangentSpace (𝓡 n) (e x),
      g.inner (e x) u u * g.inner (e x) v v - (g.inner (e x) u v) ^ 2 ≠ 0 →
        D.sectionalCurvature (e x) u v = 1)
    (θ w : EuclideanSpace ℝ (Fin n)) (hθ : inner ℝ θ θ = 1)
    (hw : inner ℝ w θ = 0) {b : ℝ} (hb : 0 < b)
    (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U) {t : ℝ} (ht : t ∈ Icc 0 b) :
    t ^ 2 * g.inner (e (t • θ))
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w) =
        Real.sin t ^ 2 * inner ℝ w w := by
  let q : ℝ → M := fun s => e (s • θ)
  let I : Set ℝ := {s | s • θ ∈ U}
  let J : (s : ℝ) → TangentSpace (𝓡 n) (q s) :=
    fun s => mfderiv (𝓡 n) (𝓡 n) e (s • θ) (s • w)
  have hI : IsOpen I := hU.preimage (by fun_prop)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ q I := by
    intro s hs
    exact ((he.contMDiffAt (hU.mem_nhds hs)).comp s
      (show ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun r : ℝ => r • θ) s from
        contMDiffAt_iff_contDiffAt.mpr (by fun_prop))).contMDiffWithinAt
  have hg := g.isGeodesicOn_all_rays_of_neighborhood (hU.mem_nhds h0) hgeo
  have he0 := he.contMDiffAt (hU.mem_nhds h0)
  have hvel0 : mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1 = mfderiv (𝓡 n) (𝓡 n) e 0 θ := by
    have h := radial_velocity_eq_differential (e := e) (t := 0) θ
      (by simpa only [zero_smul] using he0.mdifferentiableAt (by simp))
    erw [zero_smul] at h
    exact h
  have hJderiv : manifoldCovDerivAlong g q J 1 0 = mfderiv (𝓡 n) (𝓡 n) e 0 w := by
    have hline : Continuous (fun s : ℝ => s • θ) := by fun_prop
    have hfield : (fun s => mfderiv 𝓘(ℝ, ℝ) (𝓡 n)
        (fun r : ℝ => e (s • (θ + r • w))) 0 1) =ᶠ[𝓝 (0 : ℝ)] J := by
      filter_upwards [hline.continuousAt.preimage_mem_nhds
        (hU.mem_nhds (show (0 : ℝ) • θ ∈ U by simpa only [zero_smul] using h0))]
        with s hs
      exact radialVariation_field_eq θ w s
        ((he.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt (by simp))
    rw [← g.manifoldCovDerivAlong_congr_field q hfield]
    exact g.radialVariation_initial_covariantDerivative he0 θ w
  have hunit : g.inner (q 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = 1 := by
    rw [hvel0]
    change g.inner (e ((0 : ℝ) • θ)) _ _ = 1
    erw [zero_smul, hmetric]
    exact hθ
  have hn : g.inner (q 0) (manifoldCovDerivAlong g q J 1 0)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) q 0 1) = 0 := by
    rw [hJderiv, hvel0]
    change g.inner (e ((0 : ℝ) • θ)) _ _ = 0
    erw [zero_smul, hmetric]
    exact hw
  have h := normalJacobi_inner_self D hb hI hq hsub (hg θ) hunit J
    (fun s hs => contDiffAt_chartField_radialDifferential hU he θ w hs
      (mem_extChartAt_source _))
    (fun s hs => g.radialDifferential_covariant_jacobi D hU he hg θ w (hsub s hs))
    (fun s hs => hsec (s • θ) (hsub s hs)) (by simp [J]) hn ht
  rw [hJderiv] at h
  simp only [J, q, map_smul, smul_apply, smul_eq_mul] at h
  erw [zero_smul, hmetric] at h
  nlinarith only [h]

theorem normalExponential_inner
    (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hU : IsOpen U) (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hgeo : ∀ v ∈ U, g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
        (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v)
    (hsec : ∀ x ∈ U, ∀ u v : TangentSpace (𝓡 n) (e x),
      g.inner (e x) u u * g.inner (e x) v v - (g.inner (e x) u v) ^ 2 ≠ 0 →
        D.sectionalCurvature (e x) u v = 1)
    (θ w z : EuclideanSpace ℝ (Fin n)) (hθ : inner ℝ θ θ = 1)
    (hw : inner ℝ w θ = 0) (hz : inner ℝ z θ = 0) {b : ℝ} (hb : 0 < b)
    (hsub : ∀ s ∈ Icc 0 b, s • θ ∈ U) {t : ℝ} (ht : t ∈ Icc 0 b) :
    t ^ 2 * g.inner (e (t • θ))
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) z) =
        Real.sin t ^ 2 * inner ℝ w z := by
  have h := normalExponential_inner_self D hU h0 he hgeo hmetric hsec θ
    (w + z) hθ (by simp [inner_add_left, hw, hz]) hb hsub ht
  have hw' := normalExponential_inner_self D hU h0 he hgeo hmetric hsec θ w hθ hw hb hsub ht
  have hz' := normalExponential_inner_self D hU h0 he hgeo hmetric hsec θ z hθ hz hb hsub ht
  simp only [map_add, add_apply, inner_add_left, inner_add_right,
    g.symm (e (t • θ)) (mfderiv (𝓡 n) (𝓡 n) e (t • θ) z)
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)] at h
  rw [real_inner_comm w z] at h
  nlinarith only [h, hw', hz']

theorem sphericalExponential_inner
    (D : LeviCivitaData g) {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (hR : 0 < R) (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ Metric.ball 0 R})
    (hmetric : ∀ u v : EuclideanSpace ℝ (Fin n),
      g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
        (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v)
    (hsec : ∀ x ∈ Metric.ball 0 R, ∀ u v : TangentSpace (𝓡 n) (e x),
      g.inner (e x) u u * g.inner (e x) v v - (g.inner (e x) u v) ^ 2 ≠ 0 →
        D.sectionalCurvature (e x) u v = 1)
    (θ w z : EuclideanSpace ℝ (Fin n)) (hθ : inner ℝ θ θ = 1)
    {t : ℝ} (ht : 0 ≤ t) (htR : t < R) :
    t ^ 2 * g.inner (e (t • θ))
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) z) =
      Real.sin t ^ 2 * inner ℝ w z +
        (t ^ 2 - Real.sin t ^ 2) * inner ℝ w θ * inner ℝ z θ := by
  rcases ht.eq_or_lt with rfl | ht
  · simp
  have hθnorm : ‖θ‖ = 1 := by
    rw [real_inner_self_eq_norm_sq] at hθ
    nlinarith [norm_nonneg θ]
  have hsub (s : ℝ) (hs : s ∈ Icc 0 t) : s • θ ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg hs.1, hθnorm, mul_one]
    exact hs.2.trans_lt htR
  have htmem := hsub t ⟨ht.le, le_rfl⟩
  have hrad (u : EuclideanSpace ℝ (Fin n)) :
      g.inner (e (t • θ)) (mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ)
        (mfderiv (𝓡 n) (𝓡 n) e (t • θ) u) = inner ℝ θ u := by
    have h := g.radial_gauss_identity D he hmetric hgeo (t • θ) htmem u
    simp only [map_smul, smul_apply, smul_eq_mul, real_inner_smul_left] at h
    exact mul_left_cancel₀ (ne_of_gt ht) h
  have hw : inner ℝ (w - inner ℝ w θ • θ) θ = 0 := by
    simp only [inner_sub_left, real_inner_smul_left, hθ, mul_one, sub_self]
  have hz : inner ℝ (z - inner ℝ z θ • θ) θ = 0 := by
    simp only [inner_sub_left, real_inner_smul_left, hθ, mul_one, sub_self]
  have h := normalExponential_inner D Metric.isOpen_ball (by simpa using hR)
    he hgeo hmetric hsec θ (w - inner ℝ w θ • θ) (z - inner ℝ z θ • θ)
    hθ hw hz ht hsub ⟨ht.le, le_rfl⟩
  have hrw : g.inner (e (t • θ)) (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)
      (mfderiv (𝓡 n) (𝓡 n) e (t • θ) θ) = inner ℝ w θ := by
    rw [g.symm, hrad, real_inner_comm w θ]
  simp only [map_sub, sub_apply, map_smul, smul_apply, smul_eq_mul,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    hrw, hrad, hθ] at h
  rw [real_inner_comm z θ] at h
  nlinarith only [h]

theorem exists_spherical_exponential [T2Space M] [CompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : ∀ (x : M) (u v : TangentSpace (𝓡 n) x),
      g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 →
        D.sectionalCurvature x u v = 1) (p : M) :
    ∃ e : EuclideanSpace ℝ (Fin n) → M,
      e 0 = p ∧ ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 1) ∧
      (∀ u v : EuclideanSpace ℝ (Fin n),
        g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
          (mfderiv (𝓡 n) (𝓡 n) e 0 v) = inner ℝ u v) ∧
      (∀ v ∈ Metric.ball 0 1,
        g.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ Metric.ball 0 1}) ∧
      ∀ (θ w z : EuclideanSpace ℝ (Fin n)), inner ℝ θ θ = 1 →
        ∀ t : ℝ, 0 ≤ t → t < 1 →
          t ^ 2 * g.inner (e (t • θ))
            (mfderiv (𝓡 n) (𝓡 n) e (t • θ) w)
            (mfderiv (𝓡 n) (𝓡 n) e (t • θ) z) =
          Real.sin t ^ 2 * inner ℝ w z +
            (t ^ 2 - Real.sin t ^ 2) * inner ℝ w θ * inner ℝ z θ := by
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p (R := 1)
      (by norm_num) isClosed_closure.isCompact
  have hmetric := g.pullbackCoefficients_zero_of_orthonormal p
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp))) he0 hed hL
  refine ⟨e, he0, he, hmetric, fun v hv => (hgeo v hv).1, ?_⟩
  intro θ w z hθ t ht ht1
  exact sphericalExponential_inner D (by norm_num) he (fun v hv => (hgeo v hv).1)
    hmetric (fun x _ => hsec (e x)) θ w z hθ ht ht1

end PoincareConjecture.SpaceForm
