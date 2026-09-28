import PoincareConjecture.Proofs.M35.CapGeometry.RadialMetricLower
import PoincareConjecture.Proofs.M35.CapGeometry.RadialBallVolume
import PoincareConjecture.Proofs.M35.Thm12_28.TransportedVolume
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.Uniqueness

local notation "V" => StandardCapSpace

private theorem calibrated_euclidean_volume (A : Set V) :
    calibratedMetricVolume (RiemannianMetric.euclideanMetric 3) A = volume A := by
  have hiso : @Isometry V V inferInstance
      (RiemannianMetric.euclideanMetric 3).toEMetricSpace.toPseudoEMetricSpace id := by
    intro x y
    exact RiemannianMetric.euclideanMetric_edist x y
  have hhaus := @Isometry.hausdorffMeasure_image V V
    (inferInstance : EMetricSpace V) (RiemannianMetric.euclideanMetric 3).toEMetricSpace
    inferInstance inferInstance inferInstance inferInstance id (3 : ℝ) hiso
    (Or.inl (by norm_num)) A
  simp only [image_id] at hhaus
  change euclideanVolumeCalibration 3 *
    @Measure.hausdorffMeasure V (RiemannianMetric.euclideanMetric 3).toEMetricSpace
      inferInstance inferInstance (3 : ℝ) A = _
  rw [hhaus]
  simpa only [Measure.smul_apply, smul_eq_mul, Nat.cast_ofNat] using
    congrArg (fun mu : Measure V => mu A) (M10.euclideanVolumeCalibration_smul_hausdorff 3)

variable (g : RiemannianMetric 3 V) (D : LeviCivitaData g)
  (hrotation : ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ,
    ∀ x u v : V,
      g.inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = g.inner x u v)
  (hcomplete : MetricComplete g) (hsec : D.NonnegativeSectionalCurvature)

include D hsec hrotation hcomplete




theorem radial_ambient_ball_volume_lower (P : M35StandardCapPredecessors)
    {R m r : ℝ} (hR : 0 < R) (hm0 : 0 < m) (hr : 0 ≤ r)
    (hm : m ≤ intrinsicWarpingRadius g hrotation hcomplete R / R)
    (y : V) (hball : g.ball y r ⊆ g.ball 0 R) :
    ENNReal.ofReal (m ^ 3 * (Real.pi * 4 / 3) * r ^ 3) ≤
      calibratedMetricVolume g (g.ball y r) := by
  let phi := (intrinsicSpatialDiffeomorph g hrotation hcomplete).symm.toPartialDiffeomorph
  let A := Metric.ball (intrinsicSpatialCoordinate g y) r
  have himage : phi '' A ⊆ g.ball y r := by
    rintro z ⟨u, hu, rfl⟩
    change g.edist y (intrinsicSpatialInverse g hrotation hcomplete u) < ENNReal.ofReal r
    have h := intrinsicSpatialInverse_edist_le g D hrotation hcomplete hsec
      (intrinsicSpatialCoordinate g y) u
    rw [intrinsicSpatialInverse_coordinate] at h
    apply h.trans_lt
    rw [edist_dist, dist_comm]
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg (dist_nonneg : 0 ≤ dist u _)).mpr hu
  have hAU : A ⊆ Metric.ball (0 : V) R := by
    intro u hu
    have h := hball (himage (mem_image_of_mem phi hu))
    change intrinsicSpatialInverse g hrotation hcomplete u ∈ g.ball 0 R at h
    rw [← intrinsicSpatialInverse_image_ball g hrotation hcomplete P R] at h
    obtain ⟨v, hv, heq⟩ := h
    have heq' := congrArg (intrinsicSpatialCoordinate g) heq
    simp only [intrinsicSpatialCoordinate_inverse] at heq'
    exact heq' ▸ hv
  have hvolume := calibratedVolume_le_image_of_tangentNorm_lower
    (RiemannianMetric.euclideanMetric 3) g phi Metric.isOpen_ball
    (fun _ _ => mem_univ _) (inv_nonneg.mpr hm0.le) (fun u hu v => by
      rw [RiemannianMetric.euclideanMetric_tangentNorm]
      have huR : ‖u‖ ≤ R :=
        (by simpa only [Metric.mem_ball, dist_zero_right] using hu : ‖u‖ < R).le
      have h := intrinsicSpatialInverse_tangentNorm_lower
        g D hrotation hcomplete hsec hR hm0.le hm huR v
      have hh := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hm0.le)
      rw [← mul_assoc, inv_mul_cancel₀ hm0.ne', one_mul] at hh
      convert! hh using 1) Metric.isOpen_ball hAU
  rw [calibrated_euclidean_volume] at hvolume
  have hbound : volume A ≤ ENNReal.ofReal (m⁻¹ ^ 3) *
      calibratedMetricVolume g (g.ball y r) :=
    hvolume.trans (mul_le_mul' le_rfl (measure_mono himage))
  have hcancel : ENNReal.ofReal (m ^ 3) * ENNReal.ofReal (m⁻¹ ^ 3) = 1 := by
    rw [← ENNReal.ofReal_mul (pow_nonneg hm0.le _), ← mul_pow,
      mul_inv_cancel₀ hm0.ne', one_pow, ENNReal.ofReal_one]
  have hscaled := mul_le_mul' (le_refl (ENNReal.ofReal (m ^ 3))) hbound
  rw [← mul_assoc, hcancel, one_mul] at hscaled
  change ENNReal.ofReal (m ^ 3) * volume (Metric.ball _ r) ≤ _ at hscaled
  rw [EuclideanSpace.volume_ball_fin_three, ← ENNReal.ofReal_pow hr] at hscaled
  convert! hscaled using 1
  rw [← ENNReal.ofReal_mul (pow_nonneg hr _),
    ← ENNReal.ofReal_mul (pow_nonneg hm0.le _)]
  congr 1
  ring

end PoincareConjecture.M35.Uniqueness
