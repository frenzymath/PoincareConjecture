import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyOperator











set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture.M65Branch




theorem integral_norm_inv_closedBall_le_global {R : ℝ} (hR : 0 < R) (z : ℂ) :
    (∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹) ≤ 8 * Real.pi * R := by
  have hi (x : ℂ) (r : ℝ) :
      IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (closedBall x r) := by
    simpa only [norm_inv, IntegrableOn] using
      ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
        (isCompact_closedBall x r)).norm
  by_cases hz : ‖z‖ ≤ 2 * R
  · have hsub : closedBall (0 : ℂ) R ⊆ ball z (4 * R) := by
      intro w hw
      have hdist := dist_triangle w (0 : ℂ) z
      have hwR := mem_closedBall.mp hw
      simp only [dist_zero_right, dist_zero_left] at hdist hwR
      exact mem_ball.mpr (by linarith)
    calc
      _ ≤ ∫ w in ball z (4 * R), ‖z - w‖⁻¹ :=
        setIntegral_mono_set ((hi z (4 * R)).mono_set ball_subset_closedBall)
          (ae_of_all _ (fun _ => inv_nonneg.mpr (norm_nonneg _)))
          (ae_of_all _ (fun _ hw => hsub hw))
      _ = 2 * Real.pi * (4 * R) := integral_norm_inv_ball_center z (by positivity)
      _ = _ := by ring
  · have hvol : volume.real (closedBall (0 : ℂ) R) = Real.pi * R ^ 2 := by
      simp [Measure.real, hR.le, mul_comm]
    calc
      _ ≤ ∫ _w : ℂ in closedBall (0 : ℂ) R, R⁻¹ := by
        apply integral_mono_ae (hi 0 R)
          (integrableOn_const (isCompact_closedBall (0 : ℂ) R).measure_lt_top.ne)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with w hw
        have hwR : ‖w‖ ≤ R := mem_closedBall_zero_iff.mp hw
        have hnorm := norm_sub_norm_le z w
        have hlower : R ≤ ‖z - w‖ := by linarith
        simpa only [one_div] using one_div_le_one_div_of_le hR hlower
      _ = Real.pi * R := by
        rw [setIntegral_const, smul_eq_mul, hvol]
        field_simp
      _ ≤ _ := by nlinarith [Real.pi_pos]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]




theorem norm_cauchyOperator_le [CompleteSpace E] {h : ℂ → E} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : Continuous h)
    (hsupport : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hbound : ∀ w ∈ closedBall (0 : ℂ) R, ‖h w‖ ≤ B) (z : ℂ) :
    ‖cauchyOperator h z‖ ≤ 8 * R * B := by
  have hs : HasCompactSupport h :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure
      (closure_minimal hsupport isClosed_closedBall)
  have hzero (w : ℂ) (hw : w ∉ closedBall (0 : ℂ) R) : h w = 0 :=
    Function.notMem_support.mp (fun h => hw (hsupport h))
  have heq : (∫ w : ℂ, (z - w)⁻¹ • h w) =
      ∫ w in closedBall (0 : ℂ) R, (z - w)⁻¹ • h w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun w hw => by rw [hzero w hw, smul_zero])).symm
  have hk : IntegrableOn (fun w : ℂ => ‖z - w‖⁻¹) (closedBall (0 : ℂ) R) := by
    simpa only [norm_inv, IntegrableOn] using
      ((locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
        (isCompact_closedBall (0 : ℂ) R)).norm
  have hint : ‖∫ w in closedBall (0 : ℂ) R, (z - w)⁻¹ • h w‖ ≤
      (8 * Real.pi * R) * B := by
    calc
      _ ≤ ∫ w in closedBall (0 : ℂ) R, ‖(z - w)⁻¹ • h w‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹ * B := by
        apply integral_mono_ae (integrable_cauchyOperator hh hs z).integrableOn.norm
          (hk.mul_const B)
        filter_upwards [ae_restrict_mem measurableSet_closedBall] with w hw
        rw [norm_smul, norm_inv]
        exact mul_le_mul_of_nonneg_left (hbound w hw) (inv_nonneg.mpr (norm_nonneg _))
      _ = (∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹) * B := integral_mul_const B _
      _ ≤ _ := mul_le_mul_of_nonneg_right (integral_norm_inv_closedBall_le_global hR z) hB
  rw [cauchyOperator, heq, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((8 * Real.pi * R) * B) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr Real.pi_pos.le)
    _ = 8 * R * B := by field_simp

end PoincareConjecture.M65Branch
