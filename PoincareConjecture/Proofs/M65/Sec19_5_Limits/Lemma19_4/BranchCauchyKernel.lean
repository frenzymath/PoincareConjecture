import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Group.Integral

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture.M65Branch

theorem locallyIntegrable_cauchyKernel :
    LocallyIntegrable (fun w : ℂ => w⁻¹) volume := by
  apply locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp) (by simp)
  · filter_upwards with w
    simp [norm_inv, Real.rpow_neg_one]
  · exact measurable_inv.aestronglyMeasurable

theorem integral_norm_inv_ball {R : ℝ} (hR : 0 ≤ R) :
    (∫ w in ball (0 : ℂ) R, ‖w‖⁻¹) = 2 * Real.pi * R := by
  have hpolar := integral_fun_norm_addHaar (volume : Measure ℂ)
    ((Iio R).indicator fun r : ℝ => r⁻¹)
  have hleft : (fun w : ℂ => (Iio R).indicator (fun r : ℝ => r⁻¹) ‖w‖) =
      (ball (0 : ℂ) R).indicator (fun w => ‖w‖⁻¹) := by
    funext w
    simp [indicator]
  rw [hleft, integral_indicator measurableSet_ball] at hpolar
  have hradial : (∫ r in Ioi (0 : ℝ),
      r ^ (Module.finrank ℝ ℂ - 1) • (Iio R).indicator (fun s : ℝ => s⁻¹) r) = R := by
    calc
      _ = ∫ r in Ioi (0 : ℝ), (Iio R).indicator (fun _ : ℝ => 1) r := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        by_cases hrR : r < R
        · simp [hrR, mul_inv_cancel₀ (ne_of_gt (mem_Ioi.mp hr))]
        · simp [hrR]
      _ = ∫ r in Ioo (0 : ℝ) R, (1 : ℝ) := by
        rw [setIntegral_indicator measurableSet_Iio]
        congr 1
      _ = R := by simp [Measure.real, Real.volume_Ioo, hR]
  rw [hradial] at hpolar
  simpa [Measure.real, Complex.volume_ball, smul_eq_mul, mul_assoc] using hpolar

theorem locallyIntegrable_cauchyKernel_sub (z : ℂ) :
    LocallyIntegrable (fun w : ℂ => (z - w)⁻¹) volume := by
  have h := locallyIntegrable_map_homeomorph (Homeomorph.subLeft z)
    (μ := volume) (f := fun w : ℂ => w⁻¹)
  change LocallyIntegrable (fun w : ℂ => w⁻¹)
    (Measure.map (fun w => z - w) volume) ↔
      LocallyIntegrable (fun w : ℂ => (z - w)⁻¹) volume at h
  rw [Measure.map_sub_left_eq_self] at h
  exact h.mp locallyIntegrable_cauchyKernel

theorem integral_norm_inv_ball_center (z : ℂ) {R : ℝ} (hR : 0 ≤ R) :
    (∫ w in ball z R, ‖z - w‖⁻¹) = 2 * Real.pi * R := by
  calc
    _ = ∫ w : ℂ, (ball (0 : ℂ) R).indicator (fun v => ‖v‖⁻¹) (z - w) := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      filter_upwards with w
      have hm : z - w ∈ ball (0 : ℂ) R ↔ w ∈ ball z R := by
        simp [dist_eq_norm, norm_sub_rev]
      by_cases hw : w ∈ ball z R <;> simp [indicator, hm, hw]
    _ = ∫ w in ball (0 : ℂ) R, ‖w‖⁻¹ := by
      rw [integral_sub_left_eq_self, integral_indicator measurableSet_ball]
    _ = _ := integral_norm_inv_ball hR

theorem integral_norm_inv_closedBall_le {R : ℝ} (hR : 0 < R)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    (∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹) ≤ 6 * Real.pi * R := by
  have hi : IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (ball z (3 * R)) := by
    have h : IntegrableOn (fun w : ℂ => ‖(z - w)⁻¹‖) (closedBall z (3 * R)) :=
      ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
        (isCompact_closedBall z (3 * R))).norm
    simpa only [norm_inv] using h.mono_set ball_subset_closedBall
  have hsub : closedBall (0 : ℂ) R ⊆ ball z (3 * R) := by
    intro w hw
    have hdist := dist_triangle w (0 : ℂ) z
    have hwR := mem_closedBall.mp hw
    have hzR := mem_closedBall.mp hz
    rw [dist_comm 0 z] at hdist
    exact mem_ball.mpr (by linarith)
  calc
    _ ≤ ∫ w in ball z (3 * R), ‖z - w‖⁻¹ :=
      setIntegral_mono_set hi (ae_of_all _ (fun _ => inv_nonneg.mpr (norm_nonneg _)))
        (ae_of_all _ (fun _ hw => hsub hw))
    _ = 2 * Real.pi * (3 * R) := integral_norm_inv_ball_center z (by positivity)
    _ = _ := by ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem integrableOn_cauchyIntegrand {h : ℂ → E} {R : ℝ}
    (hh : ContinuousOn h (closedBall (0 : ℂ) R)) (z : ℂ) :
    IntegrableOn (fun w => (z - w)⁻¹ • h w) (closedBall (0 : ℂ) R) :=
  ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)).smul_continuousOn hh (isCompact_closedBall _ _)

theorem norm_cauchyIntegral_le [CompleteSpace E] {h : ℂ → E} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : ContinuousOn h (closedBall (0 : ℂ) R))
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖h w‖ ≤ B)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R) :
    ‖(Real.pi : ℂ)⁻¹ • ∫ w in closedBall (0 : ℂ) R, (z - w)⁻¹ • h w‖ ≤
      6 * R * B := by
  have hk : IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (closedBall (0 : ℂ) R) := by
    simpa only [norm_inv, IntegrableOn] using
      ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R)).norm
  have hint : ‖∫ w in closedBall (0 : ℂ) R, (z - w)⁻¹ • h w‖ ≤
      (6 * Real.pi * R) * B := by
    calc
      _ ≤ ∫ w in closedBall (0 : ℂ) R, ‖(z - w)⁻¹ • h w‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹ * B := by
        apply integral_mono_ae (integrableOn_cauchyIntegrand hh z).norm (hk.mul_const B)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with w hw
        rw [norm_smul, norm_inv]
        exact mul_le_mul_of_nonneg_left (hbound w hw) (inv_nonneg.mpr (norm_nonneg _))
      _ = (∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹) * B := integral_mul_const B _
      _ ≤ _ := mul_le_mul_of_nonneg_right (integral_norm_inv_closedBall_le hR hz) hB
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((6 * Real.pi * R) * B) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr Real.pi_pos.le)
    _ = 6 * R * B := by field_simp

end PoincareConjecture.M65Branch
