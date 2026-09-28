import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyDisk

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Metric Complex
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M65Branch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem hasCompactSupport_dbar {ψ : ℂ → E} (hs : HasCompactSupport ψ) :
    HasCompactSupport (dbar ψ) :=
  (hs.fderiv ℝ).comp_left (ContinuousLinearMap.map_zero dbarLinear)

theorem integral_inv_smul_dbar [CompleteSpace E] {ψ : ℂ → E}
    (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    Integrable (fun w : ℂ => w⁻¹ • dbar ψ w) ∧
      (∫ w : ℂ, w⁻¹ • dbar ψ w) = -(Real.pi : ℂ) • ψ 0 := by
  refine ⟨locallyIntegrable_cauchyKernel.integrable_smul_right_of_hasCompactSupport
    (continuous_dbar hψ) (hasCompactSupport_dbar hs), ?_⟩
  obtain ⟨R, hR, hsupport⟩ := hs.isCompact.isBounded.subset_ball_lt 0 (0 : ℂ)
  have hz (w : ℂ) (hw : w ∉ ball (0 : ℂ) R) : dbar ψ w = 0 := by
    change dbarLinear (fderiv ℝ ψ w) = 0
    rw [fderiv_of_notMem_tsupport ℝ (fun h => hw (hsupport h)), map_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := ball (0 : ℂ) R) (fun w hw => by rw [hz w hw, smul_zero])]
  rw [(integral_inv_smul_dbar_ball hψ hR).2]
  have hcircle (θ : ℝ) : ψ (circleMap 0 R θ) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro h
    have hlt := mem_ball_zero_iff.mp (hsupport h)
    have hn : ‖circleMap 0 R θ‖ = R := by simp [abs_of_pos hR]
    rw [hn] at hlt
    exact hlt.false
  simp only [hcircle, intervalIntegral.integral_zero, zero_sub, smul_neg]
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  simp only [RCLike.ofReal_eq_complex_ofReal, ofReal_mul, ofReal_ofNat, smul_smul]
  module

theorem cauchyOperator_dbar [CompleteSpace E] {h : ℂ → E}
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (z : ℂ) :
    cauchyOperator (dbar h) z = h z := by
  let ψ := fun w : ℂ => h (z - w)
  have hψ : ContDiff ℝ 1 ψ := hh.comp (contDiff_const.sub contDiff_id)
  have hsψ : HasCompactSupport ψ := hs.comp_homeomorph (Homeomorph.subLeft z)
  have hd (w : ℂ) : dbar ψ w = -dbar h (z - w) := by
    have hD := (hh.differentiable one_ne_zero (z - w)).hasFDerivAt.comp w
      ((hasFDerivAt_id (𝕜 := ℝ) w).const_sub z)
    change HasFDerivAt ψ _ w at hD
    simp only [dbar, hD.fderiv, dbarLinear, smul_apply, add_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.comp_apply,
      neg_apply, ContinuousLinearMap.id_apply, map_neg, smul_neg]
    module
  have hfund := (integral_inv_smul_dbar hψ hsψ).2
  simp only [hd, smul_neg, integral_neg, ψ, sub_zero, neg_smul] at hfund
  have hJ : (∫ w : ℂ, w⁻¹ • dbar h (z - w)) = (Real.pi : ℂ) • h z :=
    neg_injective hfund
  have hchange : (∫ w : ℂ, w⁻¹ • dbar h (z - w)) =
      ∫ w : ℂ, (z - w)⁻¹ • dbar h w := by
    simpa only [sub_sub_cancel] using integral_sub_left_eq_self
      (fun w : ℂ => (z - w)⁻¹ • dbar h w) volume z
  rw [cauchyOperator, ← hchange, hJ, smul_smul,
    inv_mul_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero), one_smul]

theorem dbar_cauchyOperator [CompleteSpace E] {h : ℂ → E}
    (hh : ContDiff ℝ 1 h) (hs : HasCompactSupport h) (z : ℂ) :
    dbar (cauchyOperator h) z = h z := by
  have hi (v : ℂ) : Integrable (fun w : ℂ => (z - w)⁻¹ • fderiv ℝ h w v) :=
    integrable_cauchyOperator
      ((hh.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hs.fderiv_apply ℝ v) z
  have hint : (∫ w : ℂ, (z - w)⁻¹ • dbar h w) =
      (2 : ℂ)⁻¹ • ((∫ w : ℂ, (z - w)⁻¹ • fderiv ℝ h w 1) +
        I • (∫ w : ℂ, (z - w)⁻¹ • fderiv ℝ h w I)) := by
    calc
      _ = ∫ w : ℂ, (2 : ℂ)⁻¹ • ((z - w)⁻¹ • fderiv ℝ h w 1 +
          I • ((z - w)⁻¹ • fderiv ℝ h w I)) := by
        apply integral_congr_ae
        apply ae_of_all
        intro w
        simp only [dbar, dbarLinear, smul_apply, add_apply,
          ContinuousLinearMap.apply_apply, smul_add, smul_smul]
        module
      _ = _ := by
        have hI : Integrable (fun w : ℂ => I • ((z - w)⁻¹ • fderiv ℝ h w I)) :=
          (hi I).smul I
        rw [integral_smul, integral_add (hi 1) hI, integral_smul]
  calc
    _ = cauchyOperator (dbar h) z := by
      simp only [dbar, dbarLinear, smul_apply, add_apply,
        ContinuousLinearMap.apply_apply, fderiv_cauchyOperator_apply hh hs]
      change (2 : ℂ)⁻¹ • (cauchyOperator (fun w => fderiv ℝ h w 1) z +
        I • cauchyOperator (fun w => fderiv ℝ h w I) z) = cauchyOperator (dbar h) z
      rw [cauchyOperator, cauchyOperator, cauchyOperator, hint]
      simp only [smul_add, smul_smul]
      module
    _ = h z := cauchyOperator_dbar hh hs z

end PoincareConjecture.M65Branch
