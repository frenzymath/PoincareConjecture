import PoincareConjecture.Proofs.M60.Mathlib.CauchyTransformKernel
import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture.M60

noncomputable def cauchyKernelNorm : ℝ := ∫ w : ℂ, ‖cauchyTransformKernel w‖

theorem cauchyKernelNorm_nonneg : 0 ≤ cauchyKernelNorm :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem norm_fderiv_cauchyTransform_le
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedSpace ℝ W] [IsScalarTower ℝ ℂ W]
    {f : ℂ → W} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    {B : ℝ} (hB : 0 ≤ B) (hDf : ∀ z, ‖fderiv ℝ f z‖ ≤ B) (z : ℂ) :
    ‖fderiv ℝ (cauchyTransform f) z‖ ≤ cauchyKernelNorm * B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg cauchyKernelNorm_nonneg hB)
  intro d
  rw [fderiv_cauchyTransform_apply hf hc]
  calc
    ‖cauchyTransform (fun w => fderiv ℝ f w d) z‖ ≤ cauchyKernelNorm * (B * ‖d‖) :=
      norm_cauchyTransform_le (fun w =>
        ((fderiv ℝ f w).le_opNorm d).trans
          (mul_le_mul_of_nonneg_right (hDf w) (norm_nonneg d))) z
    _ = cauchyKernelNorm * B * ‖d‖ := by ring

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]

theorem contDiff_operator_mul {A B : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) :
    ContDiff ℝ 1 (fun z => A z * B z) :=
  ((ContinuousLinearMap.compL ℂ V V V).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp
    (hA.prodMk hB)

theorem norm_fderiv_operator_mul_le
    {A B : ℂ → V →L[ℂ] V} {z : ℂ}
    (hA : DifferentiableAt ℝ A z) (hB : DifferentiableAt ℝ B z) :
    ‖fderiv ℝ (fun w => A w * B w) z‖ ≤
      ‖A z‖ * ‖fderiv ℝ B z‖ + ‖fderiv ℝ A z‖ * ‖B z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro d
  let C := (ContinuousLinearMap.compL ℂ V V V).bilinearRestrictScalars ℝ
  have hd := (C.isBoundedBilinearMap.hasFDerivAt (A z, B z)).comp z
    (hA.hasFDerivAt.prodMk hB.hasFDerivAt)
  change HasFDerivAt (fun w => A w * B w) _ z at hd
  rw [hd.fderiv]
  change ‖A z * fderiv ℝ B z d + fderiv ℝ A z d * B z‖ ≤ _
  calc
    _ ≤ ‖A z‖ * ‖fderiv ℝ B z d‖ + ‖fderiv ℝ A z d‖ * ‖B z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ ‖A z‖ * (‖fderiv ℝ B z‖ * ‖d‖) +
        (‖fderiv ℝ A z‖ * ‖d‖) * ‖B z‖ := by
      gcongr
      · exact (fderiv ℝ B z).le_opNorm d
      · exact (fderiv ℝ A z).le_opNorm d
    _ = (‖A z‖ * ‖fderiv ℝ B z‖ + ‖fderiv ℝ A z‖ * ‖B z‖) * ‖d‖ := by ring

noncomputable def holomorphicFrameTerm (A : ℂ → V →L[ℂ] V) :
    ℕ → ℂ → V →L[ℂ] V
  | 0 => fun _ => 1
  | j + 1 => cauchyTransform (fun z => A z * holomorphicFrameTerm A j z)

theorem contDiff_holomorphicFrameTerm {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A) (j : ℕ) :
    ContDiff ℝ 1 (holomorphicFrameTerm A j) := by
  induction j with
  | zero => exact contDiff_const
  | succ j ih => exact contDiff_cauchyTransform (contDiff_operator_mul hA ih) hc.mul_right

theorem holomorphicFrameTerm_bounds {A : ℂ → V →L[ℂ] V}
    (hA : ContDiff ℝ 1 A) (hc : HasCompactSupport A)
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 ≤ q)
    (hsmall : 2 * cauchyKernelNorm * a ≤ q)
    (hAb : ∀ z, ‖A z‖ ≤ a) (hDAb : ∀ z, ‖fderiv ℝ A z‖ ≤ a) :
    ∀ j z, ‖holomorphicFrameTerm A j z‖ ≤ q ^ j ∧
      ‖fderiv ℝ (holomorphicFrameTerm A j) z‖ ≤ q ^ j := by
  have hCa : cauchyKernelNorm * a ≤ q := by
    nlinarith [mul_nonneg cauchyKernelNorm_nonneg ha]
  intro j
  induction j with
  | zero =>
      intro z
      constructor
      · exact ContinuousLinearMap.norm_id_le
      · change ‖fderiv ℝ (fun _ : ℂ => (1 : V →L[ℂ] V)) z‖ ≤ q ^ 0
        rw [fderiv_const_apply, pow_zero]
        rw [ContinuousLinearMap.opNorm_zero]
        exact zero_le_one
  | succ j ih =>
      have hU := contDiff_holomorphicFrameTerm hA hc j
      have hprod := contDiff_operator_mul hA hU
      have hprodC : HasCompactSupport (fun z => A z * holomorphicFrameTerm A j z) :=
        hc.mul_right
      have hb (z : ℂ) : ‖A z * holomorphicFrameTerm A j z‖ ≤ a * q ^ j :=
        (norm_mul_le _ _).trans (mul_le_mul (hAb z) (ih z).1 (norm_nonneg _) ha)
      have hDb (z : ℂ) :
          ‖fderiv ℝ (fun w => A w * holomorphicFrameTerm A j w) z‖ ≤
            2 * a * q ^ j := by
        apply (norm_fderiv_operator_mul_le
          ((hA.differentiable (by simp)) z) ((hU.differentiable (by simp)) z)).trans
        calc
          _ ≤ a * q ^ j + a * q ^ j := by
            gcongr
            · exact hAb z
            · exact (ih z).2
            · exact hDAb z
            · exact (ih z).1
          _ = 2 * a * q ^ j := by ring
      intro z
      constructor
      · calc
          ‖holomorphicFrameTerm A (j + 1) z‖ ≤ cauchyKernelNorm * (a * q ^ j) :=
            norm_cauchyTransform_le hb z
          _ = (cauchyKernelNorm * a) * q ^ j := by ring
          _ ≤ q * q ^ j := mul_le_mul_of_nonneg_right hCa (pow_nonneg hq _)
          _ = q ^ (j + 1) := by rw [pow_succ]; ring
      · calc
          ‖fderiv ℝ (holomorphicFrameTerm A (j + 1)) z‖ ≤
              cauchyKernelNorm * (2 * a * q ^ j) :=
            norm_fderiv_cauchyTransform_le hprod hprodC (by positivity) hDb z
          _ = (2 * cauchyKernelNorm * a) * q ^ j := by ring
          _ ≤ q * q ^ j := mul_le_mul_of_nonneg_right hsmall (pow_nonneg hq _)
          _ = q ^ (j + 1) := by rw [pow_succ]; ring

end PoincareConjecture.M60
