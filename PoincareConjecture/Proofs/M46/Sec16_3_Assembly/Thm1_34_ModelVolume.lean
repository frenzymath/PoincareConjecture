import PoincareConjecture.Proofs.M15.Thm1_34_VolumeComparison










set_option autoImplicit false

open Set MeasureTheory

namespace PoincareConjecture.Proofs.M46


theorem sinh_le_cosh_mul {A z : ℝ} (hz : z ∈ Icc 0 A) :
    Real.sinh z ≤ Real.cosh A * z := by
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun x (_hx : x ∈ Icc (0 : ℝ) A) =>
      (Real.hasDerivAt_sinh x).hasDerivWithinAt)
    (fun x (hx : x ∈ Ico (0 : ℝ) A) => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos x)]
      exact Real.cosh_strictMonoOn.monotoneOn hx.1 (hz.1.trans hz.2) hx.2.le) z hz
  simpa only [Real.sinh_zero, sub_zero, Real.norm_eq_abs,
    abs_of_nonneg (Real.sinh_nonneg_iff.mpr hz.1)] using h


theorem modelS_scaled_inv_sq_le {A R t : ℝ} (hA : 0 < A) (hR : 0 < R)
    (ht : t ∈ Icc 0 R) :
    RiemannianMetric.modelS ((A / R) ^ 2) t ≤ Real.cosh A * t := by
  have hQ : 0 < A / R := div_pos hA hR
  have hz : (A / R) * t ∈ Icc (0 : ℝ) A := by
    refine ⟨mul_nonneg hQ.le ht.1, ?_⟩
    calc
      (A / R) * t ≤ (A / R) * R := mul_le_mul_of_nonneg_left ht.2 hQ.le
      _ = A := div_mul_cancel₀ A hR.ne'
  rw [RiemannianMetric.modelS, if_neg (pow_ne_zero 2 hQ.ne'), Real.sqrt_sq hQ.le]
  apply (div_le_iff₀ hQ).mpr
  simpa only [mul_left_comm, mul_assoc, mul_comm] using sinh_le_cosh_mul hz


theorem modelVolume_scaled_inv_sq_le {A R : ℝ} (hA : 0 < A) (hR : 0 < R) :
    RiemannianMetric.modelVolume 3 ((A / R) ^ 2) R ≤
      Real.cosh A ^ 2 * RiemannianMetric.euclideanUnitBallVolume 3 * R ^ 3 := by
  have hprofile : ∀ t ∈ Icc (0 : ℝ) R,
      RiemannianMetric.modelS ((A / R) ^ 2) t ^ 2 ≤ Real.cosh A ^ 2 * t ^ 2 := by
    intro t ht
    simpa only [mul_pow] using pow_le_pow_left₀
      (RiemannianMetric.modelS_nonneg (sq_nonneg _) ht.1)
      (modelS_scaled_inv_sq_le hA hR ht) 2
  have hintegral := intervalIntegral.integral_mono_on hR.le
    (RiemannianMetric.intervalIntegrable_modelS_pow 3 ((A / R) ^ 2) 0 R)
    ((continuous_const.mul (continuous_id.pow 2)).intervalIntegrable 0 R) hprofile
  calc
    RiemannianMetric.modelVolume 3 ((A / R) ^ 2) R ≤
        3 * RiemannianMetric.euclideanUnitBallVolume 3 *
          ∫ t in (0 : ℝ)..R, Real.cosh A ^ 2 * t ^ 2 :=
      mul_le_mul_of_nonneg_left hintegral
        (mul_nonneg (by norm_num) (RiemannianMetric.euclideanUnitBallVolume_nonneg 3))
    _ = _ := by rw [intervalIntegral.integral_const_mul, integral_pow]; norm_num; ring


theorem scaled_smallBallVolumeBound_ge {A R s k : ℝ}
    (hA : 0 < A) (hR : 0 < R) (hs : 0 < s) (hk : 0 < k) :
    (Real.cosh A)⁻¹ ^ 2 * k * s ^ 3 ≤
      RiemannianMetric.smallerBallVolumeBound 3 ((A / R) ^ 2) R (k * R ^ 3) s := by
  have hw := RiemannianMetric.euclideanUnitBallVolume_pos 3
  have hc := Real.cosh_pos A
  have hden := RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3)
    (sq_nonneg (A / R)) hR
  have hnum := RiemannianMetric.euclidean_modelVolume_le_modelVolume
    (by norm_num : 1 ≤ 3) (sq_nonneg (A / R)) hs.le
  calc
    (Real.cosh A)⁻¹ ^ 2 * k * s ^ 3 =
        (RiemannianMetric.euclideanUnitBallVolume 3 * s ^ 3 /
          (Real.cosh A ^ 2 * RiemannianMetric.euclideanUnitBallVolume 3 * R ^ 3)) *
            (k * R ^ 3) := by
      field_simp [hw.ne', hc.ne', hR.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (div_le_div₀ (RiemannianMetric.modelVolume_pos (by norm_num : 1 ≤ 3)
        (sq_nonneg (A / R)) hs).le hnum hden
        (modelVolume_scaled_inv_sq_le hA hR)) (by positivity)

end PoincareConjecture.Proofs.M46
