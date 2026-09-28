import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingEndpoint
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Variation.Manifold













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_pullback_modelOn
    (N : IntrinsicAnnulus) {gamma V : ℝ → AnnulusCoordinates}
    {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (hgamma : DifferentiableAt ℝ gamma t) (hV : ContDiffOn ℝ ∞ V J) :
    rampHorizontalCovariantDerivative N.connection gamma V t =
      deriv V t + coordinateChristoffel N.metric.euclideanCoefficients (gamma t)
        (deriv gamma t) (V t) := by
  have hfield (v : AnnulusCoordinates) :
      Proofs.M09.chartVectorField 0 v = (fun _ : AnnulusCoordinates => v) := by
    simp only [Proofs.M09.chartVectorField, chartAt_self_eq]
    change VectorField.mpullback (𝓡 2) (𝓡 2) id (fun _ => v) = (fun _ => v)
    exact VectorField.mpullback_id
  have h := M62.pullback_chart_field N.connection 0 hgamma.mdifferentiableAt
    (by simp) hJ ht V hV
  simp only [hfield] at h
  rw [h, N.connection.connection_const_eq_inverse]
  congr 1
  rw [m64Intrinsic_curveVelocity_eq_deriv]
  rfl




theorem m64Intrinsic_pullback_coordinate_transport
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates} (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U)
    {u V : ℝ → AnnulusCoordinates} {J : Set ℝ} (hJ : IsOpen J)
    (hu : ContDiffOn ℝ ∞ u J) (hV : ContDiffOn ℝ ∞ V J)
    (hmap : MapsTo u J U) {t : ℝ} (ht : t ∈ J)
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (u t))) :
    rampHorizontalCovariantDerivative N.connection (e ∘ u)
        (fun s => fderiv ℝ e (u s) (V s)) t =
      fderiv ℝ e (u t)
        (deriv V t + coordinateChristoffel (N.metric.pullbackCoefficients e) (u t)
          (deriv u t) (V t)) := by
  have heu := he.contDiffAt (hU.mem_nhds (hmap ht))
  have hut := hu.contDiffAt (hJ.mem_nhds ht)
  have hVt := hV.contDiffAt (hJ.mem_nhds ht)
  have hde : ContDiffOn ℝ ∞ (fderiv ℝ e) U := fun x hx =>
    ((he.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).contDiffWithinAt
  have hpush : ContDiffOn ℝ ∞ (fun s => fderiv ℝ e (u s) (V s)) J :=
    (hde.comp hu hmap).clm_apply hV
  have hbase : DifferentiableAt ℝ (e ∘ u) t :=
    (heu.differentiableAt (by simp)).comp t (hut.differentiableAt (by simp))
  have hif : Function.Injective (fderiv ℝ e (u t)) := by
    simpa only [mfderiv_eq_fderiv] using! hi
  have hmetric (y a b : AnnulusCoordinates) :
      N.metric.pullbackCoefficients e y a b =
        N.metric.euclideanCoefficients (e y) (fderiv ℝ e y a) (fderiv ℝ e y b) := by
    change N.metric.inner (e y) (mfderiv (𝓡 2) (𝓡 2) e y a)
      (mfderiv (𝓡 2) (𝓡 2) e y b) = _
    rw [mfderiv_eq_fderiv]
    rfl
  have h := ConnectionVariation.covDerivAlong_change_coordinates
    ((N.metric.contDiffAt_pullbackCoefficients
      (contMDiffAt_iff_contDiffAt.mpr heu)).differentiableAt (by simp))
    ((N.metric.contDiffAt_euclideanCoefficients (e (u t))).differentiableAt (by simp))
    (N.metric.isInvertible_pullbackCoefficients hi) (N.metric.inner_isInvertible _)
    (Eventually.of_forall fun y a b => N.metric.symm _ _ _)
    (Eventually.of_forall fun y a b => N.metric.symm _ _ _)
    heu (LinearMap.surjective_of_injective (f := (fderiv ℝ e (u t)).toLinearMap) hif)
    (Eventually.of_forall hmetric)
    (hut.differentiableAt (by simp)) (hVt.differentiableAt (by simp)) (1 : ℝ)
  exact (m64Intrinsic_pullback_modelOn N hJ ht hbase hpush).trans (by
    simpa only [ConnectionVariation.covDerivAlong, fderiv_eq_smul_deriv,
      one_smul] using! h)




theorem m64Intrinsic_pullback_congr_base
    (N : IntrinsicAnnulus) {gamma eta V : ℝ → AnnulusCoordinates}
    {J : Set ℝ} (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (hgamma : DifferentiableAt ℝ gamma t) (heta : DifferentiableAt ℝ eta t)
    (hV : ContDiffOn ℝ ∞ V J) (hge : gamma =ᶠ[𝓝 t] eta) :
    rampHorizontalCovariantDerivative N.connection gamma V t =
      rampHorizontalCovariantDerivative N.connection eta V t := by
  rw [m64Intrinsic_pullback_modelOn N hJ ht hgamma hV,
    m64Intrinsic_pullback_modelOn N hJ ht heta hV, hge.deriv_eq, hge.self_of_nhds]




theorem m64Intrinsic_pushed_radial_pairing
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (x w : AnnulusCoordinates) (c : ℝ)
    (hgauss : ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e x x v = inner ℝ x v) :
    N.metric.inner (e x) (fderiv ℝ e x (c • x)) (fderiv ℝ e x w) =
      c * inner ℝ x w := by
  have h : N.metric.pullbackCoefficients e x (c • x) w = c * inner ℝ x w := by
    rw [map_smul, smul_apply, smul_eq_mul, hgauss]
  change N.metric.inner (e x) (mfderiv (𝓡 2) (𝓡 2) e x (c • x))
    (mfderiv (𝓡 2) (𝓡 2) e x w) = _ at h
  simpa only [mfderiv_eq_fderiv] using! h



theorem m64Intrinsic_pushed_focusing_norm
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    {x : AnnulusCoordinates} (hx : 0 < ‖x‖) {kappa : ℝ} (hkappa : 0 < kappa)
    (hpi : kappa * ‖x‖ < Real.pi)
    (hgauss : ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e x x v = inner ℝ x v) :
    N.metric.tangentNorm (e x)
      (fderiv ℝ e x ((Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x)) =
        Real.sin (kappa * ‖x‖) / kappa := by
  let c := Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)
  have hc : 0 < c := div_pos
    (Real.sin_pos_of_pos_of_lt_pi (mul_pos hkappa hx) hpi) (mul_pos hkappa hx)
  rw [RiemannianMetric.tangentNorm,
    m64Intrinsic_pushed_radial_pairing N e x (c • x) c hgauss]
  rw [inner_smul_right, real_inner_self_eq_norm_sq]
  rw [show c * (c * ‖x‖ ^ 2) = (c * ‖x‖) ^ 2 by ring,
    Real.sqrt_sq (mul_pos hc hx).le]
  dsimp only [c]
  field_simp




theorem m64Intrinsic_pushed_boundary_focusing
    (N : IntrinsicAnnulus) {e : AnnulusCoordinates → AnnulusCoordinates}
    {U : Set AnnulusCoordinates} (hU : IsOpen U) (he : ContDiffOn ℝ ∞ e U)
    {u V : ℝ → AnnulusCoordinates} {J : Set ℝ} (hJ : IsOpen J)
    (hu : ContDiffOn ℝ ∞ u J) (hV : ContDiffOn ℝ ∞ V J)
    (hmap : MapsTo u J U) {radius : ℝ} (hradius : radius ≠ 0)
    (hboundary : ∀ s ∈ J, e (u s) = intrinsicAnnulusBoundary radius s)
    {t C : ℝ} (ht : t ∈ J)
    (hi : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e (u t)))
    (hquadratic : C * N.metric.pullbackCoefficients e (u t) (deriv u t) (deriv u t) ≤
      N.metric.pullbackCoefficients e (u t)
        (deriv V t + coordinateChristoffel (N.metric.pullbackCoefficients e) (u t)
          (deriv u t) (V t)) (deriv u t)) :
    C * intrinsicBoundarySpeed N.metric radius t ≤
      N.metric.inner (intrinsicAnnulusBoundary radius t)
        (rampHorizontalCovariantDerivative N.connection (intrinsicAnnulusBoundary radius)
          (fun s => fderiv ℝ e (u s) (V s)) t)
        (intrinsicBoundaryUnitTangent N.metric radius t) := by
  let gamma := intrinsicAnnulusBoundary radius
  let W : ℝ → AnnulusCoordinates := fun s => fderiv ℝ e (u s) (V s)
  let A := deriv V t + coordinateChristoffel (N.metric.pullbackCoefficients e) (u t)
    (deriv u t) (V t)
  have heu := he.contDiffAt (hU.mem_nhds (hmap ht))
  have hut := hu.contDiffAt (hJ.mem_nhds ht)
  have hde : ContDiffOn ℝ ∞ (fderiv ℝ e) U := fun x hx =>
    ((he.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := ∞) (by simp)).contDiffWithinAt
  have hW : ContDiffOn ℝ ∞ W J := (hde.comp hu hmap).clm_apply hV
  have hbase : DifferentiableAt ℝ (e ∘ u) t :=
    (heu.differentiableAt (by simp)).comp t (hut.differentiableAt (by simp))
  have hgamma : DifferentiableAt ℝ gamma t :=
    (m64Intrinsic_contDiff_boundary radius).contDiffAt.differentiableAt (by simp)
  have hge : (e ∘ u) =ᶠ[𝓝 t] gamma := by
    filter_upwards [hJ.mem_nhds ht] with s hs
    exact hboundary s hs
  have hv : curveVelocity (n := 2) gamma t = fderiv ℝ e (u t) (deriv u t) := by
    rw [m64Intrinsic_curveVelocity_eq_deriv, ← hge.deriv_eq]
    exact ((heu.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt
      (l := e) (f := u) t (hut.differentiableAt (by simp)).hasDerivAt).deriv
  have hD : rampHorizontalCovariantDerivative N.connection gamma W t =
      fderiv ℝ e (u t) A :=
    (m64Intrinsic_pullback_congr_base N hJ ht hgamma hbase hW hge.symm).trans
      (m64Intrinsic_pullback_coordinate_transport N hU he hJ hu hV hmap ht hi)
  have hB (v w : AnnulusCoordinates) :
      N.metric.pullbackCoefficients e (u t) v w =
        N.metric.inner (gamma t) (fderiv ℝ e (u t) v) (fderiv ℝ e (u t) w) := by
    change N.metric.inner (e (u t)) (mfderiv (𝓡 2) (𝓡 2) e (u t) v)
      (mfderiv (𝓡 2) (𝓡 2) e (u t) w) = _
    rw [mfderiv_eq_fderiv, hboundary t ht]
    rfl
  have hspeed := m64Intrinsic_boundarySpeed_pos N hradius t
  have hspeedSq : intrinsicBoundarySpeed N.metric radius t ^ 2 =
      N.metric.pullbackCoefficients e (u t) (deriv u t) (deriv u t) := by
    rw [hB, ← hv]
    exact Real.sq_sqrt (Real.sqrt_pos.mp hspeed).le
  change C * intrinsicBoundarySpeed N.metric radius t ≤
    N.metric.inner (gamma t) (rampHorizontalCovariantDerivative N.connection gamma W t)
      ((intrinsicBoundarySpeed N.metric radius t)⁻¹ • curveVelocity (n := 2) gamma t)
  rw [hD, map_smul, smul_eq_mul, hv, ← hB]
  have h := mul_le_mul_of_nonneg_left hquadratic (inv_pos.mpr hspeed).le
  rw [← hspeedSq] at h
  convert! h using 1
  field_simp

end PoincareConjecture
