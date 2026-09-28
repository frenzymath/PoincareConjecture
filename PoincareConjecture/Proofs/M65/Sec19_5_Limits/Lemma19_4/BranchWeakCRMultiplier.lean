import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyWeakInverse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

theorem dbar_mul {p q : ℂ → ℂ} {z : ℂ}
    (hp : DifferentiableAt ℝ p z) (hq : DifferentiableAt ℝ q z) :
    dbar (fun w => p w * q w) z = dbar p z * q z + p z * dbar q z := by
  have hd := hp.hasFDerivAt.mul hq.hasFDerivAt
  change HasFDerivAt (fun w => p w * q w) _ z at hd
  simp only [dbar, hd.fderiv, dbarLinear, smul_apply, add_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  ring

theorem weak_dbar_mul_C1 {F G q : ℂ → ℂ} {U : Set ℂ}
    (hF : LocallyIntegrable F volume) (hG : LocallyIntegrable G volume)
    (hq : ContDiff ℝ 1 q)
    (hweak : ∀ φ : ℂ → ℂ, ContDiff ℝ 1 φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ z, dbar φ z * F z) = -∫ z, φ z * G z)
    (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ) (hs : HasCompactSupport φ)
    (hU : tsupport φ ⊆ U) :
    (∫ z, dbar φ z * (q z * F z)) =
      -∫ z, φ z * (dbar q z * F z + q z * G z) := by
  have hqd := continuous_dbar hq
  have hφd := continuous_dbar hφ
  have hbars : HasCompactSupport (dbar φ) := by
    apply hs.of_isClosed_subset (isClosed_tsupport _)
    exact (tsupport_comp_subset (map_zero dbarLinear) (fderiv ℝ φ)).trans
      (tsupport_fderiv_subset ℝ)
  have hi (f : ℂ → ℂ) (hc : Continuous f) (hf : HasCompactSupport f) :
      Integrable (fun z => f z * F z) := by
    simpa only [smul_eq_mul] using hF.integrable_smul_left_of_hasCompactSupport hc hf
  have hiA : Integrable (fun z => (dbar φ z * q z) * F z) :=
    hi _ (hφd.mul hq.continuous) hbars.mul_right
  have hiB : Integrable (fun z => (φ z * dbar q z) * F z) :=
    hi _ (hφ.continuous.mul hqd) hs.mul_right
  have hiC : Integrable (fun z => (φ z * q z) * G z) := by
    simpa only [smul_eq_mul, Pi.mul_apply] using hG.integrable_smul_left_of_hasCompactSupport
      (hφ.continuous.mul hq.continuous) hs.mul_right
  have htest := hweak (fun z => φ z * q z) (hφ.mul hq) hs.mul_right
    (tsupport_mul_subset_left.trans hU)
  have hprod (z : ℂ) : dbar (fun w => φ w * q w) z =
      dbar φ z * q z + φ z * dbar q z :=
    dbar_mul (hφ.differentiable one_ne_zero z) (hq.differentiable one_ne_zero z)
  simp_rw [hprod, add_mul] at htest
  rw [integral_add hiA hiB] at htest
  have heq : (∫ z, (dbar φ z * q z) * F z) =
      -((∫ z, (φ z * dbar q z) * F z) + ∫ z, (φ z * q z) * G z) := by
    linear_combination htest
  calc
    _ = ∫ z, (dbar φ z * q z) * F z := by simp_rw [mul_assoc]
    _ = _ := heq
    _ = _ := by
      rw [← integral_add hiB hiC]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      ring

end PoincareConjecture.M65Branch
