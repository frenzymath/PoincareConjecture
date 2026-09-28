import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RadialEndpoint
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_FocusingNorm














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem m64Intrinsic_contDiffAt_focusing_field
    {kappa : ℝ} (hkappa : kappa ≠ 0)
    {x : AnnulusCoordinates} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞
      (fun y : AnnulusCoordinates =>
        (Real.sin (kappa * ‖y‖) / (kappa * ‖y‖)) • y) x := by
  have hn : ContDiffAt ℝ ∞ (norm : AnnulusCoordinates → ℝ) x :=
    contDiffAt_norm ℝ hx
  exact (((contDiffAt_const.mul hn).sin).div
    (contDiffAt_const.mul hn) (mul_ne_zero hkappa (norm_ne_zero_iff.mpr hx))).smul
      contDiffAt_id



theorem m64Intrinsic_pushed_focusing_norm_le_sin_radius
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    {x : AnnulusCoordinates} (hx : 0 < ‖x‖) {kappa R : ℝ}
    (hkappa : 0 < kappa) (hxR : ‖x‖ ≤ R)
    (hRhalf : kappa * R ≤ Real.pi / 2)
    (hgauss : ∀ v : AnnulusCoordinates,
      N.metric.pullbackCoefficients e x x v = inner ℝ x v) :
    N.metric.tangentNorm (e x)
        (fderiv ℝ e x
          ((Real.sin (kappa * ‖x‖) / (kappa * ‖x‖)) • x)) ≤
      Real.sin (kappa * R) / kappa := by
  have hangle : kappa * ‖x‖ ≤ kappa * R :=
    mul_le_mul_of_nonneg_left hxR hkappa.le
  have hpi : kappa * ‖x‖ < Real.pi := by
    linarith [hangle.trans hRhalf, Real.pi_pos]
  rw [m64Intrinsic_pushed_focusing_norm N e hx hkappa hpi hgauss]
  apply div_le_div_of_nonneg_right _ hkappa.le
  apply Real.sin_le_sin_of_le_of_le_pi_div_two _ hRhalf hangle
  linarith [mul_pos hkappa hx, Real.pi_pos]




theorem m64Intrinsic_focusing_at_of_radial_segment
    (N : IntrinsicAnnulus) (K : ℝ) (hK : N.GaussianCurvatureBound K)
    {e : AnnulusCoordinates → AnnulusCoordinates} {U : Set AnnulusCoordinates}
    (hU : IsOpen U) (h0 : (0 : AnnulusCoordinates) ∈ U)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e U)
    (hgeo : ∀ v ∈ U,
      N.metric.IsGeodesicOn (fun s : ℝ => e (s • v)) {s | s • v ∈ U})
    (hmetric : ∀ v w : AnnulusCoordinates,
      N.metric.inner (e 0) (mfderiv (𝓡 2) (𝓡 2) e 0 v)
        (mfderiv (𝓡 2) (𝓡 2) e 0 w) = inner ℝ v w)
    (hgauss : ∀ v ∈ U, ∀ w : AnnulusCoordinates,
      N.metric.pullbackCoefficients e v v w = inner ℝ v w)
    {x : AnnulusCoordinates} (hx : x ≠ 0)
    (hpi : Real.sqrt (max K 1) * ‖x‖ < Real.pi)
    (hsub : ∀ s ∈ Icc (0 : ℝ) 1, s • x ∈ U)
    (hmap : ∀ s ∈ Ioo (0 : ℝ) 1, e (s • x) ∈ standardAnnulusDomain) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 2) e x) ∧
      ∀ w : AnnulusCoordinates,
        let kappa := Real.sqrt (max K 1)
        let B := N.metric.pullbackCoefficients e
        let Y : AnnulusCoordinates → AnnulusCoordinates :=
          fun y => (Real.sin (kappa * ‖y‖) / (kappa * ‖y‖)) • y
        Real.cos (kappa * ‖x‖) * B x w w ≤
          B x (fderiv ℝ Y x w + coordinateChristoffel B x w (Y x)) w := by
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let theta : AnnulusCoordinates := ‖x‖⁻¹ • x
  have htheta : ‖theta‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxpos),
      inv_mul_cancel₀ hxpos.ne']
  obtain ⟨basis, hbasis⟩ :=
    RiemannianMetric.exists_orthonormalBasis_radial (m := 1) theta htheta
  have hradial (s : ℝ) : s • basis 0 = (s / ‖x‖) • x := by
    rw [hbasis]
    simp only [theta, smul_smul, div_eq_mul_inv]
  have hend : ‖x‖ • basis 0 = x := by
    rw [hradial, div_self hxpos.ne', one_smul]
  have hsub' (s : ℝ) (hs : s ∈ Icc (0 : ℝ) ‖x‖) : s • basis 0 ∈ U := by
    rw [hradial]
    apply hsub (s / ‖x‖)
    exact ⟨div_nonneg hs.1 hxpos.le, (div_le_one hxpos).mpr hs.2⟩
  have hmap' (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) ‖x‖) :
      e (s • basis 0) ∈ standardAnnulusDomain := by
    rw [hradial]
    apply hmap (s / ‖x‖)
    exact ⟨div_pos hs.1 hxpos, (div_lt_one hxpos).mpr hs.2⟩
  have hkappa : 0 < Real.sqrt (max K 1) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (le_max_right K 1))
  have hKkappa : K ≤ Real.sqrt (max K 1) ^ 2 := by
    rw [Real.sq_sqrt (zero_le_one.trans (le_max_right K 1))]
    exact le_max_left K 1
  have hinj := m64Intrinsic_radial_mfderiv_injective_of_gaussian_upper
    N K (Real.sqrt (max K 1)) hK hkappa hKkappa hU h0 he hgeo hmetric
    (basis 0) (basis.norm_eq_one 0) hxpos hpi hsub' hmap'
    ‖x‖ ⟨hxpos.le, le_rfl⟩
  refine ⟨?_, ?_⟩
  · rw [← hend]
    exact hinj
  · intro w
    have hfocus := m64Intrinsic_focusing_pairing_ge_of_gaussian_upper_Ioc
      N K hK hU h0 he hgeo hmetric hgauss basis hxpos hpi hsub' hmap'
      (r := ‖x‖) ⟨hxpos, le_rfl⟩ w
    simpa only [hend] using hfocus

end PoincareConjecture
