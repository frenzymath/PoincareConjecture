import PoincareConjecture.Proofs.M60.Mathlib.CauchyRiemannGauge
import Mathlib.Analysis.Calculus.FDeriv.Symmetric










set_option autoImplicit false

open Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M60

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]



noncomputable def complexGradient (C : E →L[ℝ] V) (u : ℂ → E) (z : ℂ) : V :=
  C (fderiv ℝ u z 1) - I • C (fderiv ℝ u z I)



theorem contDiffAt_complexGradient (C : E →L[ℝ] V) {u : ℂ → E} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) : ContDiffAt ℝ 1 (complexGradient C u) z := by
  have hd := hu.fderiv_right (m := 1) (by norm_num)
  exact (C.contDiff.contDiffAt.comp z (hd.clm_apply contDiffAt_const)).sub
    ((C.contDiff.contDiffAt.comp z (hd.clm_apply contDiffAt_const)).const_smul I)




theorem cauchyRiemannDerivative_complexGradient
    (C : E →L[ℝ] V) {u : ℂ → E} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) :
    cauchyRiemannDerivative (complexGradient C u) z =
      (1 / 2 : ℝ) • C (fderiv ℝ (fderiv ℝ u) z 1 1 +
        fderiv ℝ (fderiv ℝ u) z I I) := by
  have hd := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hcol (d : ℂ) : HasFDerivAt (fun w => C (fderiv ℝ u w d))
      (C.comp ((fderiv ℝ (fderiv ℝ u) z).flip d)) z := by
    have h := C.hasFDerivAt.comp z
      (hd.hasFDerivAt.clm_apply (hasFDerivAt_const d z))
    simpa only [Function.comp_def, fderiv_const, ContinuousLinearMap.comp_zero,
      zero_add] using h
  have hW := (hcol 1).sub ((hcol I).const_smul I)
  change HasFDerivAt (complexGradient C u) _ z at hW
  have hsym := (hu.isSymmSndFDerivAt (by norm_num)).eq 1 I
  unfold cauchyRiemannDerivative
  rw [hW.fderiv]
  simp only [sub_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, map_add, smul_sub, smul_smul, I_mul_I,
    neg_one_smul, sub_neg_eq_add, hsym]
  congr 1
  abel

end PoincareConjecture.M60
