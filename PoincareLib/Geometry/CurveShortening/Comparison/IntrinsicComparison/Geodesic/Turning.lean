import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Metric.Germ
import PoincareLib.Geometry.Riemannian.Surface.GaussBonnet.SideIntegrals
import PoincareLib.Geometry.Riemannian.Curvature.Euclidean
import PoincareLib.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension

/-!
# Vanishing turning along actual reparametrized geodesics

The intrinsic geodesic equation gives zero covariant derivative for any
ambient extension of its velocity, also after a smooth change of parameter.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareMT

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

/-- The genuine intrinsic geodesic equation gives the displayed derivative of the original
coordinate velocity. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, including
the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional construction is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`,
Mathematical Checks. -/
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

/-- A constant multiple of geodesic velocity remains parallel after an arbitrary
differentiable parameter change. Only the actual field germ along that curve is used.
Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, including the Gauss--Bonnet
argument in Lemma 19.45, p. 474; the explicit regional construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
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

/-- The normalized tangent of a regular reparametrized unit geodesic has zero retained
covariant derivative. Its tangent sign is locally constant. Source: Morgan--Tian Proposition
19.35, printed pp. 467-481, including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the
explicit regional construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
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

/-- The normalized tangent of the actual regular reparametrized unit geodesic has zero
surface turning form. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481, including
the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional construction is
reviewed in `proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`,
Mathematical Checks. -/
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

end PoincareMT
