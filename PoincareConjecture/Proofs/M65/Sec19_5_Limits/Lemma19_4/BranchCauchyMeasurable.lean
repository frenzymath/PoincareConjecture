import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyBound

set_option autoImplicit false

open Set MeasureTheory Metric
open scoped Topology

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem integrable_cauchyOperator_of_bound {h : ℂ → E} {R B : ℝ}
    (hh : AEStronglyMeasurable h volume)
    (hsupport : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hbound : ∀ w, ‖h w‖ ≤ B) (z : ℂ) :
    Integrable (fun w : ℂ => (z - w)⁻¹ • h w) := by
  have hk := (locallyIntegrable_cauchyKernel_sub z).integrableOn_isCompact
    (isCompact_closedBall (0 : ℂ) R)
  have hm : AEStronglyMeasurable (fun w : ℂ => (z - w)⁻¹ • h w) volume :=
    ((measurable_const.sub measurable_id).inv.aestronglyMeasurable).smul hh
  have hi : IntegrableOn (fun w : ℂ => (z - w)⁻¹ • h w) (closedBall (0 : ℂ) R) := by
    apply (hk.norm.mul_const B).mono' hm.restrict
    filter_upwards with w
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hbound w) (norm_nonneg _)
  apply (integrableOn_iff_integrable_of_support_subset ?_).mp hi
  intro w hw
  apply hsupport
  by_contra hzero
  have hhzero : h w = 0 := Function.notMem_support.mp hzero
  exact hw (by simp only [hhzero, smul_zero])

theorem norm_cauchyOperator_le_of_bound [CompleteSpace E] {h : ℂ → E} {R B : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B) (hh : AEStronglyMeasurable h volume)
    (hsupport : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hbound : ∀ w, ‖h w‖ ≤ B) (z : ℂ) :
    ‖cauchyOperator h z‖ ≤ 8 * R * B := by
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
        apply integral_mono_ae
          (integrable_cauchyOperator_of_bound hh hsupport hbound z).integrableOn.norm
          (hk.mul_const B)
        filter_upwards with w
        rw [norm_smul, norm_inv]
        exact mul_le_mul_of_nonneg_left (hbound w) (inv_nonneg.mpr (norm_nonneg _))
      _ = (∫ w in closedBall (0 : ℂ) R, ‖z - w‖⁻¹) * B := integral_mul_const B _
      _ ≤ _ := mul_le_mul_of_nonneg_right (integral_norm_inv_closedBall_le_global hR z) hB
  rw [cauchyOperator, heq, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  calc
    _ ≤ Real.pi⁻¹ * ((8 * Real.pi * R) * B) :=
      mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr Real.pi_pos.le)
    _ = 8 * R * B := by field_simp

theorem cauchyOperator_sub_of_bound {h k : ℂ → E} {R B C : ℝ}
    (hh : AEStronglyMeasurable h volume) (hk : AEStronglyMeasurable k volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (ks : Function.support k ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) (kb : ∀ w, ‖k w‖ ≤ C) (z : ℂ) :
    cauchyOperator (h - k) z = cauchyOperator h z - cauchyOperator k z := by
  simp only [cauchyOperator, Pi.sub_apply, smul_sub]
  rw [integral_sub (integrable_cauchyOperator_of_bound hh hs hb z)
    (integrable_cauchyOperator_of_bound hk ks kb z), smul_sub]

end PoincareConjecture.M65Branch
