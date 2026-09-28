import PoincareConjecture.Proofs.M64.Mathlib.TurningFormNorm
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_NormalFrame
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GeodesicTurning

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem connection_reparam_field
    (N : IntrinsicAnnulus) {gamma eta U : ℝ → AnnulusCoordinates}
    {phi : ℝ → ℝ} {t c : ℝ}
    (hg : ContDiff ℝ ∞ gamma) (hU : ContDiff ℝ ∞ U)
    (hphi : DifferentiableAt ℝ phi t) (heta : eta =ᶠ[𝓝 t] gamma ∘ phi)
    {W : AnnulusCoordinates → AnnulusCoordinates}
    (hW : DifferentiableAt ℝ W (eta t))
    (hfield : ∀ᶠ s in 𝓝 t, W (eta s) = c • U (phi s)) :
    N.connection.connection W (eta t) (deriv eta t) =
      c • (deriv phi t • rampHorizontalCovariantDerivative N.connection gamma U (phi t)) := by
  have hdeta : HasDerivAt eta (deriv phi t • deriv gamma (phi t)) t :=
    ((hg.differentiable (by simp) _).hasDerivAt.scomp t hphi.hasDerivAt).congr_of_eventuallyEq heta
  have hleft := hW.hasFDerivAt.comp_hasDerivAt t hdeta
  have hright := ((hU.differentiable (by simp) _).hasDerivAt.scomp t
    hphi.hasDerivAt).const_smul c
  have hfield' : W ∘ eta =ᶠ[𝓝 t] (fun s => c • U (phi s)) := hfield
  have hderiv : fderiv ℝ W (eta t) (deriv eta t) =
      c • (deriv phi t • deriv U (phi t)) := by
    rw [hdeta.deriv]
    exact hleft.deriv.symm.trans (hfield'.deriv_eq.trans hright.deriv)
  rw [N.connection.connection_eq_fderiv_add hW, hderiv]
  change _ + N.connection.connection (fun _ => W (eta t)) (eta t) (deriv eta t) = _
  rw [N.connection.connection_const_eq_inverse, hfield.self_of_nhds, hdeta.deriv,
    heta.self_of_nhds, m64Intrinsic_pullback_model N hg hU]
  change _ + CoordinateExponential.christoffelBilinear N.metric.euclideanCoefficients
      (gamma (phi t)) (deriv phi t • deriv gamma (phi t)) (c • U (phi t)) =
    c • (deriv phi t • (deriv U (phi t) +
      CoordinateExponential.christoffelBilinear N.metric.euclideanCoefficients
        (gamma (phi t)) (deriv gamma (phi t)) (U (phi t))))
  simp only [map_smul, smul_apply, smul_add, smul_smul]

theorem m64Intrinsic_normalized_boundary_reparam_connection
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    {eta : ℝ → AnnulusCoordinates} {phi : ℝ → ℝ} {t : ℝ}
    (hphi : ContDiffAt ℝ 2 phi t) (hpd : deriv phi t ≠ 0)
    (heta : eta =ᶠ[𝓝 t] intrinsicAnnulusBoundary radius ∘ phi)
    {V : AnnulusCoordinates → AnnulusCoordinates}
    (hV : ∀ᶠ s in 𝓝 t, V (eta s) = deriv eta s)
    (hW : DifferentiableAt ℝ (fun x =>
      (N.metric.tangentNorm x (V x))⁻¹ • V x) (eta t)) :
    let W := fun x => (N.metric.tangentNorm x (V x))⁻¹ • V x
    N.metric.inner (eta t) (W (eta t)) (W (eta t)) = 1 ∧
      N.metric.tangentNorm (eta t) (N.connection.connection W (eta t) (V (eta t))) =
        |deriv phi t| *
          (intrinsicGeodesicCurvature N.metric N.connection radius (phi t) *
            intrinsicBoundarySpeed N.metric radius (phi t)) := by
  let gamma := intrinsicAnnulusBoundary radius
  let U := intrinsicBoundaryUnitTangent N.metric radius
  let W := fun x => (N.metric.tangentNorm x (V x))⁻¹ • V x
  change N.metric.inner (eta t) (W (eta t)) (W (eta t)) = 1 ∧ _
  have hg := m64Intrinsic_contDiff_boundary radius
  have hU := m64Intrinsic_contDiff_boundaryUnitTangent N hradius
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
  obtain ⟨c, hcabs, hc⟩ : ∃ c : ℝ, |c| = 1 ∧
      ∀ᶠ s in 𝓝 t, |deriv phi s|⁻¹ * deriv phi s = c := by
    rcases lt_or_gt_of_ne hpd with hn | hp
    · refine ⟨-1, by norm_num, ?_⟩
      filter_upwards [hpc.eventually (Iio_mem_nhds hn)] with s hs
      rw [abs_of_neg hs, inv_neg, neg_mul, inv_mul_cancel₀ (ne_of_lt hs)]
    · refine ⟨1, by norm_num, ?_⟩
      filter_upwards [hpc.eventually (Ioi_mem_nhds hp)] with s hs
      rw [abs_of_pos hs, inv_mul_cancel₀ (ne_of_gt hs)]
  have hfield : ∀ᶠ s in 𝓝 t, W (eta s) = c • U (phi s) := by
    filter_upwards [hvel, heta, hc] with s hs heq hcs
    have hnorm : N.metric.tangentNorm (eta s) (V (eta s)) =
        |deriv phi s| * intrinsicBoundarySpeed N.metric radius (phi s) := by
      rw [hs, heq]
      rw [m64Intrinsic_tangentNorm_smul]
      rw [intrinsicBoundarySpeed, m64Intrinsic_curveVelocity_eq_deriv]
      rfl
    change (N.metric.tangentNorm (eta s) (V (eta s)))⁻¹ • V (eta s) = _
    rw [hnorm, hs]
    change _ = c • ((intrinsicBoundarySpeed N.metric radius (phi s))⁻¹ •
      curveVelocity (n := 2) (intrinsicAnnulusBoundary radius) (phi s))
    rw [m64Intrinsic_curveVelocity_eq_deriv, mul_inv, smul_smul, smul_smul]
    congr 1
    calc
      _ = (|deriv phi s|⁻¹ * deriv phi s) *
          (intrinsicBoundarySpeed N.metric radius (phi s))⁻¹ := by ring
      _ = _ := by rw [hcs]
  have hconn := connection_reparam_field N hg hU
    (hphi.differentiableAt (by norm_num)) heta hW hfield
  have hp : eta t = intrinsicAnnulusBoundary radius (phi t) := heta.self_of_nhds
  constructor
  · change N.metric.euclideanCoefficients (eta t) (W (eta t)) (W (eta t)) = 1
    rw [hfield.self_of_nhds, hp]
    change N.metric.inner (intrinsicAnnulusBoundary radius (phi t))
      (c • U (phi t)) (c • U (phi t)) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    rw [show N.metric.inner (intrinsicAnnulusBoundary radius (phi t))
      (U (phi t)) (U (phi t)) = 1 from m64Intrinsic_boundary_unit_tangent_inner N hradius _]
    nlinarith [sq_abs c]
  · rw [hV.self_of_nhds, hconn, m64Intrinsic_tangentNorm_smul,
      m64Intrinsic_tangentNorm_smul, hcabs, one_mul]
    congr 1
    rw [m64Intrinsic_turning_density N hradius]
    change Real.sqrt (N.metric.euclideanCoefficients (eta t) _ _) =
      Real.sqrt (N.metric.euclideanCoefficients (intrinsicAnnulusBoundary radius (phi t)) _ _)
    rw [hp]

theorem m64Intrinsic_normalized_boundary_turning_bound
    (N : IntrinsicAnnulus) {radius : ℝ} (hradius : radius ≠ 0)
    (e1 e2 : AnnulusCoordinates → AnnulusCoordinates)
    {eta : ℝ → AnnulusCoordinates} {phi : ℝ → ℝ} {t : ℝ}
    (hphi : ContDiffAt ℝ 2 phi t) (hpd : deriv phi t ≠ 0)
    (heta : eta =ᶠ[𝓝 t] intrinsicAnnulusBoundary radius ∘ phi)
    {V : AnnulusCoordinates → AnnulusCoordinates}
    (hV : ∀ᶠ s in 𝓝 t, V (eta s) = deriv eta s)
    (hW : DifferentiableAt ℝ (fun x =>
      (N.metric.tangentNorm x (V x))⁻¹ • V x) (eta t))
    (he1 : N.metric.inner (eta t) (e1 (eta t)) (e1 (eta t)) = 1)
    (he2 : N.metric.inner (eta t) (e2 (eta t)) (e2 (eta t)) = 1)
    (horth : N.metric.inner (eta t) (e1 (eta t)) (e2 (eta t)) = 0) :
    |N.connection.surfaceTurningForm e1 e2
      (fun x => (N.metric.tangentNorm x (V x))⁻¹ • V x) V (eta t)| ≤
        |deriv phi t| *
          (intrinsicGeodesicCurvature N.metric N.connection radius (phi t) *
            intrinsicBoundarySpeed N.metric radius (phi t)) := by
  obtain ⟨hunit, hnorm⟩ := m64Intrinsic_normalized_boundary_reparam_connection
    N hradius hphi hpd heta hV hW
  exact (N.connection.abs_surfaceTurningForm_le_tangentNorm e1 e2 _ V (eta t)
    he1 he2 horth hunit).trans_eq hnorm

end PoincareConjecture
