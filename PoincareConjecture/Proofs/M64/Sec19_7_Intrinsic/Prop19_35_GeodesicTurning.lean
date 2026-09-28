import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MetricGerm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.SideIntegrals
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_geodesic_velocity_hasDerivAt
    (g : RiemannianMetric 2 AnnulusCoordinates)
    {gamma : ℝ → AnnulusCoordinates} {I : Set ℝ}
    (hgeo : g.IsGeodesicOn gamma I) {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (deriv gamma)
      (-coordinateChristoffel g.euclideanCoefficients (gamma t)
        (deriv gamma t) (deriv gamma t)) t := by
  have h := (hgeo.hasDerivAt_chart_at ht (gamma t) (by simp)).2
  rw [m64Intrinsic_model_chart_coefficients] at h
  simpa only [extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, id_eq] using h

theorem m64Intrinsic_connection_reparam_geodesic_eq_zero
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    {gamma eta : ℝ → AnnulusCoordinates} {phi : ℝ → ℝ} {I : Set ℝ} {t c : ℝ}
    (hgeo : g.IsGeodesicOn gamma I) (ht : phi t ∈ I)
    (hphi : DifferentiableAt ℝ phi t)
    (heta : eta =ᶠ[𝓝 t] gamma ∘ phi)
    {W : AnnulusCoordinates → AnnulusCoordinates}
    (hW : DifferentiableAt ℝ W (eta t))
    (hfield : ∀ᶠ s in 𝓝 t, W (eta s) = c • deriv gamma (phi s)) :
    D.connection W (eta t) (deriv eta t) = 0 := by
  have hgamma : DifferentiableAt ℝ gamma (phi t) :=
    contMDiffAt_iff_contDiffAt.mp (hgeo.contMDiffAt ht) |>.differentiableAt (by simp)
  have hdeta : HasDerivAt eta (deriv phi t • deriv gamma (phi t)) t :=
    (hgamma.hasDerivAt.scomp t hphi.hasDerivAt).congr_of_eventuallyEq heta
  have hleft := hW.hasFDerivAt.comp_hasDerivAt t hdeta
  have hright := ((m64Intrinsic_geodesic_velocity_hasDerivAt g hgeo ht).scomp t
    hphi.hasDerivAt).const_smul c
  have hfield' : W ∘ eta =ᶠ[𝓝 t] (fun s => c • deriv gamma (phi s)) := hfield
  have hderiv : fderiv ℝ W (eta t) (deriv eta t) =
      c • (deriv phi t • (-coordinateChristoffel g.euclideanCoefficients
        (gamma (phi t)) (deriv gamma (phi t)) (deriv gamma (phi t)))) := by
    rw [hdeta.deriv]
    exact hleft.deriv.symm.trans (hfield'.deriv_eq.trans hright.deriv)
  rw [D.connection_eq_fderiv_add hW, hderiv]
  change _ + D.connection (fun _ => W (eta t)) (eta t) (deriv eta t) = 0
  rw [D.connection_const_eq_inverse, hfield.self_of_nhds, hdeta.deriv,
    heta.self_of_nhds]
  change _ + coordinateChristoffel g.euclideanCoefficients (gamma (phi t))
    (deriv phi t • deriv gamma (phi t)) (c • deriv gamma (phi t)) = 0
  change _ + CoordinateExponential.christoffelBilinear g.euclideanCoefficients
    (gamma (phi t)) (deriv phi t • deriv gamma (phi t))
      (c • deriv gamma (phi t)) = 0
  simp only [map_smul, smul_apply, smul_neg]
  exact neg_add_cancel _

theorem m64Intrinsic_normalized_geodesic_connection_eq_zero
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    {gamma eta : ℝ → AnnulusCoordinates} {phi : ℝ → ℝ} {I : Set ℝ} {t : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : g.IsGeodesicOn gamma I) (ht : phi t ∈ I)
    (hphi : ContDiffAt ℝ 2 phi t) (hpd : deriv phi t ≠ 0)
    (heta : eta =ᶠ[𝓝 t] gamma ∘ phi)
    (hunit : ∀ᶠ s in 𝓝 (phi t), g.inner (gamma s) (deriv gamma s) (deriv gamma s) = 1)
    {V : AnnulusCoordinates → AnnulusCoordinates}
    (hV : ∀ᶠ s in 𝓝 t, V (eta s) = deriv eta s)
    (hT : DifferentiableAt ℝ (fun x =>
      (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x) (eta t)) :
    D.connection (fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x)
      (eta t) (deriv eta t) = 0 := by
  have hpc : ContinuousAt (deriv phi) t := by
    simpa only [fderiv_eq_smul_deriv, one_smul] using
      ((hphi.fderiv_right (m := 1) (by norm_num)).clm_apply
        (contDiffAt_const (c := (1 : ℝ)))).continuousAt
  have hpdiff : ∀ᶠ s in 𝓝 t, DifferentiableAt ℝ phi s :=
    (hphi.eventually (by norm_num)).mono fun _ hs => hs.differentiableAt (by norm_num)
  have hvel : ∀ᶠ s in 𝓝 t, V (eta s) = deriv phi s • deriv gamma (phi s) := by
    filter_upwards [hV, heta.deriv, hpdiff] with s hs heq hds
    rw [hs, heq]
    exact ((hg.differentiable (by simp) _).hasDerivAt.scomp s hds.hasDerivAt).deriv
  obtain ⟨c, hc⟩ : ∃ c : ℝ, ∀ᶠ s in 𝓝 t,
      |deriv phi s|⁻¹ * deriv phi s = c := by
    rcases lt_or_gt_of_ne hpd with hn | hp
    · refine ⟨-1, ?_⟩
      filter_upwards [hpc.eventually (Iio_mem_nhds hn)] with s hs
      rw [abs_of_neg hs, inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hs)]
    · refine ⟨1, ?_⟩
      filter_upwards [hpc.eventually (Ioi_mem_nhds hp)] with s hs
      rw [abs_of_pos hs, inv_mul_cancel₀ (ne_of_gt hs)]
  apply m64Intrinsic_connection_reparam_geodesic_eq_zero D hgeo ht
    (hphi.differentiableAt (by norm_num)) heta hT (c := c)
  filter_upwards [hvel, heta, hc, hphi.continuousAt.eventually hunit] with s hs heq hcs hus
  have hn : g.inner (eta s) (V (eta s)) (V (eta s)) = (deriv phi s) ^ 2 := by
    rw [hs, heq]
    simp only [Function.comp_apply, map_smul, smul_eq_mul]
    rw [g.symm _ (deriv phi s • deriv gamma (phi s)) (deriv gamma (phi s)),
      map_smul, smul_eq_mul, hus]
    ring
  rw [hn, Real.sqrt_sq_eq_abs, hs, smul_smul, hcs]

theorem m64Intrinsic_normalized_geodesic_turning_eq_zero
    {g : RiemannianMetric 2 AnnulusCoordinates} (D : LeviCivitaData g)
    (e1 e2 : AnnulusCoordinates → AnnulusCoordinates)
    {gamma eta : ℝ → AnnulusCoordinates} {phi : ℝ → ℝ} {I : Set ℝ} {t : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hgeo : g.IsGeodesicOn gamma I) (ht : phi t ∈ I)
    (hphi : ContDiffAt ℝ 2 phi t) (hpd : deriv phi t ≠ 0)
    (heta : eta =ᶠ[𝓝 t] gamma ∘ phi)
    (hunit : ∀ᶠ s in 𝓝 (phi t), g.inner (gamma s) (deriv gamma s) (deriv gamma s) = 1)
    {V : AnnulusCoordinates → AnnulusCoordinates}
    (hV : ∀ᶠ s in 𝓝 t, V (eta s) = deriv eta s)
    (hT : DifferentiableAt ℝ (fun x =>
      (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x) (eta t)) :
    D.surfaceTurningForm e1 e2
      (fun x => (Real.sqrt (g.inner x (V x) (V x)))⁻¹ • V x) V (eta t) = 0 := by
  unfold LeviCivitaData.surfaceTurningForm
  rw [hV.self_of_nhds,
    m64Intrinsic_normalized_geodesic_connection_eq_zero D hg hgeo ht hphi hpd heta hunit hV hT]
  simp

end PoincareConjecture
