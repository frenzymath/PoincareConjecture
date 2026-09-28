import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchMeasurableGauge
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyWeakInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem map_cauchyOperator_of_bound {E G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (L : E →L[ℂ] G) {h : ℂ → E} {R B : ℝ}
    (hh : AEStronglyMeasurable h volume)
    (hs : Function.support h ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ w, ‖h w‖ ≤ B) (z : ℂ) :
    L (cauchyOperator h z) = cauchyOperator (fun w => L (h w)) z := by
  rw [cauchyOperator, cauchyOperator, map_smul,
    ← L.integral_comp_comm (integrable_cauchyOperator_of_bound hh hs hb z)]
  simp only [map_smul]

theorem integral_dbar_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hs : HasCompactSupport φ) : (∫ z, dbar φ z) = 0 := by
  have hdi (v : ℂ) : Integrable (fun z => fderiv ℝ φ z v) := by
    have hc : Continuous (fun z => fderiv ℝ φ z v) :=
      (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
    exact hc.integrable_of_hasCompactSupport (hs.fderiv_apply ℝ v)
  have hz (v : ℂ) : (∫ z, fderiv ℝ φ z v) = 0 := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := φ) (g := fun _ : ℂ => (1 : ℂ)) (v := v)
      (by simpa only [mul_one] using hdi v)
      (by simp)
      (by simpa only [mul_one] using hφ.continuous.integrable_of_hasCompactSupport hs)
      (fun z _ => hφ.differentiable one_ne_zero z)
      (fun _ _ => differentiableAt_const _)
    simpa only [fderiv_const_apply, zero_apply, mul_zero, integral_zero, mul_one,
      eq_neg_iff_add_eq_zero, zero_add] using h
  simp only [dbar, dbarLinear, smul_apply, add_apply, ContinuousLinearMap.apply_apply,
    smul_eq_mul]
  rw [integral_const_mul, integral_add (hdi 1) ((hdi I).const_mul I),
    integral_const_mul, hz 1, hz I]
  ring

theorem cauchyGauge_weak_dbar_projection {B : Type*} [NormedRing B]
    [NormedAlgebra ℂ B] [CompleteSpace B] [NormOneClass B]
    {A : ℂ → B} {R B0 : ℝ}
    (hR : 0 < R) (hB : 0 ≤ B0) (hA : AEStronglyMeasurable A volume)
    (hs : Function.support A ⊆ closedBall (0 : ℂ) R)
    (hb : ∀ z, ‖A z‖ ≤ B0) (hsmall : 8 * R * B0 < 1 / 2)
    (L : B →L[ℂ] ℂ) (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hφs : HasCompactSupport φ) :
    (∫ z, dbar φ z * L (cauchyGauge A z)) =
      -∫ z, φ z * L (A z * cauchyGauge A z) := by
  have hP := cauchyGauge_measurable_spec hR hB hA hs hb hsmall
  have hPb (z : ℂ) : ‖cauchyGauge A z‖ ≤ 2 := by
    have h := norm_le_norm_sub_add (cauchyGauge A z) (1 : B)
    rw [norm_one] at h
    linarith [hP.2.2.1 z]
  let G (z : ℂ) := A z * cauchyGauge A z
  have hG : AEStronglyMeasurable G volume := hA.mul hP.1.aestronglyMeasurable
  have hGs : Function.support G ⊆ closedBall (0 : ℂ) R :=
    (Function.support_mul_subset_left _ _).trans hs
  have hGb (z : ℂ) : ‖G z‖ ≤ B0 * 2 :=
    (norm_mul_le _ _).trans (mul_le_mul (hb z) (hPb z) (norm_nonneg _) hB)
  let g (z : ℂ) := L (G z)
  have hg : AEStronglyMeasurable g volume := L.continuous.comp_aestronglyMeasurable hG
  have hgs : Function.support g ⊆ closedBall (0 : ℂ) R :=
    (Function.support_comp_subset (map_zero L) G).trans hGs
  have hgb (z : ℂ) : ‖g z‖ ≤ ‖L‖ * (B0 * 2) :=
    (L.le_opNorm (G z)).trans (mul_le_mul_of_nonneg_left (hGb z) (norm_nonneg L))
  have hgL2 : MemLp g 2 volume := memLp_of_bound_support hg hgs hgb 2
  have heq (z : ℂ) : L (cauchyGauge A z) = L 1 + cauchyOperator g z := by
    rw [hP.2.1 z, map_add, map_cauchyOperator_of_bound L hG hGs hGb]
  have hd : Continuous (dbar φ) := continuous_dbar hφ
  have hds : HasCompactSupport (dbar φ) := hasCompactSupport_dbar hφs
  have hi0 : Integrable (fun z => dbar φ z * L 1) :=
    (hd.integrable_of_hasCompactSupport hds).mul_const _
  have hi1 : Integrable (fun z => dbar φ z * cauchyOperator g z) := by
    have hc := continuous_cauchyOperator_of_bound (by positivity) hg hgs hgb
    exact (hd.mul hc).integrable_of_hasCompactSupport hds.mul_right
  simp_rw [heq, mul_add]
  rw [integral_add hi0 hi1, integral_mul_const, integral_dbar_eq_zero hφ hφs,
    zero_mul, zero_add]
  exact cauchyOperator_weak_dbar_C1 hR (by positivity) hgL2 hgs hgb φ hφ hφs

end PoincareConjecture.M65Branch
