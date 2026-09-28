import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchLocalFactor
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussMapConnection











noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Branch

variable {n : ℕ}



def coordinateComplexification : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)



def complexGradient (H : ℂ → EuclideanSpace ℝ (Fin n)) (z : ℂ) : Fin n → ℂ :=
  coordinateComplexification (fderiv ℝ H z 1) -
    I • coordinateComplexification (fderiv ℝ H z I)




theorem contDiffOn_complexGradient {H : ℂ → EuclideanSpace ℝ (Fin n)}
    {s : Set ℂ} (hs : IsOpen s) (hH : ContDiffOn ℝ ∞ H s) :
    ContDiffOn ℝ 1 (complexGradient H) s := by
  have hD : ContDiffOn ℝ 1 (fderiv ℝ H) s :=
    hH.fderiv_of_isOpen hs (WithTop.coe_le_coe.mpr le_top)
  exact (coordinateComplexification.contDiff.comp_contDiffOn
    (hD.clm_apply contDiffOn_const)).sub
      ((coordinateComplexification.contDiff.comp_contDiffOn
        (hD.clm_apply contDiffOn_const)).const_smul I)




theorem dbar_complexGradient {H : ℂ → EuclideanSpace ℝ (Fin n)} {z : ℂ}
    (hH : ContDiffAt ℝ ∞ H z) :
    dbar (complexGradient H) z = (2 : ℂ)⁻¹ • coordinateComplexification
      (fderiv ℝ (fderiv ℝ H) z 1 1 + fderiv ℝ (fderiv ℝ H) z I I) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ H) z :=
    (hH.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hsym := hH.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)
  have hc (v : ℂ) := coordinateComplexification.hasFDerivAt.comp z
    (hd.hasFDerivAt.clm_apply (hasFDerivAt_const v z))
  have hder := (hc 1).sub ((hc I).const_smul I)
  change HasFDerivAt (complexGradient H) _ z at hder
  have hactual (v : ℂ) : fderiv ℝ (complexGradient H) z v =
      coordinateComplexification (fderiv ℝ (fderiv ℝ H) z v 1) -
        I • coordinateComplexification (fderiv ℝ (fderiv ℝ H) z v I) := by
    simp only [hder.fderiv, ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
      add_apply, ContinuousLinearMap.flip_apply, zero_apply, map_zero, zero_add]
  change (2 : ℂ)⁻¹ • (fderiv ℝ (complexGradient H) z 1 +
    I • fderiv ℝ (complexGradient H) z I) = _
  rw [hactual, hactual]
  rw [hsym I 1]
  simp only [smul_sub, smul_smul, I_mul_I, neg_one_smul, sub_neg_eq_add, map_add]
  module




theorem complexGradient_eq_zero_iff (H : ℂ → EuclideanSpace ℝ (Fin n)) (z : ℂ) :
    complexGradient H z = 0 ↔ fderiv ℝ H z = 0 := by
  constructor
  · intro h
    have hcols (i : Fin n) : (fderiv ℝ H z 1) i = 0 ∧ (fderiv ℝ H z I) i = 0 := by
      have hi := congrFun h i
      change ((fderiv ℝ H z 1) i : ℂ) - I * ((fderiv ℝ H z I) i : ℂ) = 0 at hi
      have hre := congrArg Complex.re hi
      have him := congrArg Complex.im hi
      simp only [sub_re, sub_im, mul_re, mul_im, I_re, I_im, ofReal_re, ofReal_im,
        zero_mul, one_mul, mul_zero, zero_sub, sub_zero, zero_add, zero_re, zero_im] at hre him
      exact ⟨hre, neg_eq_zero.mp him⟩
    have h1 : fderiv ℝ H z 1 = 0 := by ext i; exact (hcols i).1
    have hI : fderiv ℝ H z I = 0 := by ext i; exact (hcols i).2
    apply ContinuousLinearMap.ext
    intro w
    have hw : w = w.re • (1 : ℂ) + w.im • I := by
      simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im w).symm
    rw [hw]
    simp only [map_add, map_smul, h1, hI, smul_zero, add_zero, zero_apply]
  · intro h
    simp only [complexGradient, h, zero_apply, map_zero,
      smul_zero, sub_zero]

end PoincareConjecture.M65Branch
