import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.RadialJacobi
import PoincareConjecture.Proofs.Horizon.Geometry.Alexandrov.Riemannian.Gauss
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Radial
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Toponogov.Support.Geodesic








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.RiemannianMetric.Alexandrov

open ConnectionVariation ConnectionAlongCurve CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option maxHeartbeats 1200000 in

theorem radial_pairing_le_hyperbolic
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : ∀ x u v, -1 ≤ D.sectionalCurvature x u v)
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
      (‖v‖ * Real.cosh ‖v‖ / Real.sinh ‖v‖) * g.pullbackCoefficients e v w w := by
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
  have hbound := Conjugate.jacobi_inner_le_hyperbolic_of_minimizing D
    (by linarith : -a / 2 < 0) (by linarith : 1 < (a + 1) / 2)
    isOpen_Ioo hqgeo hsub hJ hjac
    (radialVariation_field_zero e v w) (norm_pos_iff.mpr hv0) hspeed
    (by simpa only [q, zero_smul, one_smul] using hmin)
    (fun t _ u w => hsec (q t) u w)
  rw [Toponogov.radialVariation_endpoint_pairing_eq g he hv hi w] at hbound
  have hfield := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hfield
  rw [hfield] at hbound
  have hpair := congrArg (fun z : EuclideanSpace ℝ (Fin n) => g.inner (e z)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w)
    (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w))
      (one_smul ℝ v)
  rw [hpair] at hbound
  exact hbound



theorem radial_pairing_le_hyperbolic_sharp
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : ∀ x u v, -1 ≤ D.sectionalCurvature x u v)
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
      (‖v‖ * Real.cosh ‖v‖ / Real.sinh ‖v‖) * g.pullbackCoefficients e v w w +
        (1 - ‖v‖ * Real.cosh ‖v‖ / Real.sinh ‖v‖) *
          (inner ℝ v w) ^ 2 / ‖v‖ ^ 2 := by
  have hat := he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)
  have hB := (g.contDiffAt_pullbackCoefficients hat).differentiableAt (by simp)
  have hsymm : ∀ᶠ y in 𝓝 v, ∀ a b,
      g.pullbackCoefficients e y a b = g.pullbackCoefficients e y b a :=
    Eventually.of_forall fun y a b => g.symm _ _ _
  have hgauss : ∀ᶠ y in 𝓝 v, ∀ w,
      g.pullbackCoefficients e y y w = inner ℝ y w := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with y hy w
    exact g.radial_gauss_identity D he hnorm hradial y hy w
  obtain ⟨hzero, horth⟩ := CoordinateExponential.Alexandrov.radial_christoffel_identities
    hB (g.isInvertible_pullbackCoefficients hi.1) hsymm hgauss
  exact CoordinateExponential.Alexandrov.radial_quadratic_refinement
    (g.pullbackCoefficients e v) (christoffelBilinear (g.pullbackCoefficients e) v v)
    hv0 (hsymm.self_of_nhds) (hgauss.self_of_nhds) hzero horth
    (radial_pairing_le_hyperbolic g D hsec he hnorm hradial hv hv0 hi hmin) w

private theorem second_deriv_sq {r : ℝ → ℝ} {t : ℝ}
    (hr : ContDiffAt ℝ 2 r t) :
    deriv (deriv (fun s => r s ^ 2)) t =
      2 * deriv r t ^ 2 + 2 * r t * deriv (deriv r) t := by
  have hfirst : deriv (fun s => r s ^ 2) =ᶠ[𝓝 t]
      (fun s => 2 * r s * deriv r s) := by
    filter_upwards [hr.eventually (by norm_num)] with s hs
    convert! ((hs.differentiableAt (by norm_num)).hasDerivAt.pow 2).deriv using 1
    simp
  have hrd : DifferentiableAt ℝ (deriv r) t :=
    (hr.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hd := (((hr.differentiableAt (by norm_num)).hasDerivAt.const_mul 2).mul
    hrd.hasDerivAt).deriv
  change deriv (fun s => 2 * r s * deriv r s) t =
    2 * deriv r t * deriv r t + 2 * r t * deriv (deriv r) t at hd
  rw [hfirst.deriv_eq, hd]
  ring


theorem deriv2_norm_le_hyperbolic
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : ∀ x u v, -1 ≤ D.sectionalCurvature x u v)
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
    deriv (deriv (fun s => ‖u s‖)) t ≤
      (Real.cosh ‖u t‖ / Real.sinh ‖u t‖) *
        (g.pullbackCoefficients e (u t) (deriv u t) (deriv u t) -
          deriv (fun s => ‖u s‖) t ^ 2) := by
  let r : ℝ → ℝ := fun s => ‖u s‖
  have hr : ContDiffAt ℝ 2 r t := (contDiffAt_norm ℝ hut0).comp t hu
  have hrpos : 0 < r t := norm_pos_iff.mpr hut0
  have heq := g.deriv2_norm_sq_eq_precompact_radial_pairing D he hnorm hradial
    hut hi hu hgeo
  have hb := radial_pairing_le_hyperbolic_sharp g D hsec he hnorm hradial
    hut hut0 hi hmin (deriv u t)
  have hd₁ := ((hu.differentiableAt (by norm_num)).hasDerivAt.norm_sq)
  have hd₂ := ((hr.differentiableAt (by norm_num)).hasDerivAt.pow 2)
  have hdr : r t * deriv r t = inner ℝ (u t) (deriv u t) := by
    have h := hd₁.unique hd₂
    norm_num at h
    linarith
  have hrad : (inner ℝ (u t) (deriv u t)) ^ 2 / ‖u t‖ ^ 2 = deriv r t ^ 2 := by
    rw [← hdr]
    change (r t * deriv r t) ^ 2 / r t ^ 2 = _
    field_simp [ne_of_gt hrpos]
  have hsecond := second_deriv_sq hr
  change deriv (deriv (fun s => r s ^ 2)) t = _ at heq
  rw [hsecond] at heq
  simp only [mul_div_assoc] at hb
  rw [hrad] at hb
  apply (mul_le_mul_iff_of_pos_left hrpos).mp
  change r t * deriv (deriv r) t ≤ _
  nlinarith only [heq, hb]



theorem deriv2_inverse_radius_le_hyperbolic
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hsec : ∀ x u v, -1 ≤ D.sectionalCurvature x u v)
    {e : EuclideanSpace ℝ (Fin n) → M} {R : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ a b, g.pullbackCoefficients e 0 a b = inner ℝ a b)
    (hradial : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun r : ℝ => e (r • v)) {r : ℝ | r • v ∈ Metric.ball 0 R})
    (B : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (heB : EqOn e B B.source)
    (hBi : ContMDiffOn (𝓡 n) (𝓡 n) ∞ B.symm B.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) (hvB : v ∈ B.source)
    (hv0 : v ≠ 0) (hi : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible)
    (hmin : g.edist (e 0) (e v) = ENNReal.ofReal ‖v‖)
    {γ : ℝ → M} {I : Set ℝ} {t : ℝ}
    (hγ : g.IsGeodesicOn γ I) (ht : t ∈ I) (hx : e v = γ t) :
    deriv (deriv (fun s => ‖B.symm (γ s)‖)) t ≤
      (Real.cosh ‖v‖ / Real.sinh ‖v‖) *
        (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) -
            deriv (fun s => ‖B.symm (γ s)‖) t ^ 2) := by
  let u := B.symm ∘ γ
  have hxB : B v = γ t := (heB hvB).symm.trans hx
  have htB : γ t ∈ B.target := hxB ▸ B.map_source hvB
  have hut : u t = v := by dsimp [u]; rw [← hxB, B.left_inv hvB]
  have hγt := Conjugate.Realization.contMDiffAt_of_isGeodesicOn hγ ht
  have hu : ContDiffAt ℝ ∞ u t := contMDiffAt_iff_contDiffAt.mp
    ((hBi.contMDiffAt (B.open_target.mem_nhds htB)).comp t hγt)
  have hproj : (e ∘ u) =ᶠ[𝓝 t] γ := by
    filter_upwards [hγt.continuousAt.preimage_mem_nhds (B.open_target.mem_nhds htB)] with s hs
    change e (B.symm (γ s)) = γ s
    rw [heB (B.map_target hs), B.right_inv hs]
  have het : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e (u t) := by
    rw [hut]
    exact he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)
  have hit : (mfderiv (𝓡 n) (𝓡 n) e (u t)).IsInvertible := hut ▸ hi
  have hode := g.deriv2_lift_eq_neg_christoffel het hit.bijective hu hγ ht hproj
  have hbound := deriv2_norm_le_hyperbolic g D hsec he hnorm hradial
    (hut ▸ hv) (hut ▸ hv0) hit.bijective (hut ▸ hmin)
    (hu.of_le (by norm_cast)) hode
  rw [g.pullback_velocity_inner_eq_of_lift (het.mdifferentiableAt (by simp))
    (hu.differentiableAt (by simp)) hproj, hut] at hbound
  exact hbound

end PoincareConjecture.RiemannianMetric.Alexandrov
