import PoincareConjecture.Proofs.M60.Mathlib.LogQuadraticDerivative
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.RoundLaplacian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff BigOperators

namespace PoincareConjecture

theorem m60SphereParameter_logDensity_contDiff :
    ContDiff ℝ ∞ (fun z : LoopPlane => Real.log (16 / (‖z‖ ^ 2 + 4) ^ 2)) := by
  apply ContDiff.log
  · exact contDiff_const.div (((contDiff_norm_sq ℝ).add contDiff_const).pow 2)
      (by intro z; positivity)
  · intro z
    positivity

theorem m60SphereParameter_logDensity_laplacian (z : LoopPlane) :
    (∑ i : Fin 2, fderiv ℝ (fun y => fderiv ℝ
      (fun x : LoopPlane => Real.log (16 / (‖x‖ ^ 2 + 4) ^ 2)) y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) z
          (EuclideanSpace.basisFun (Fin 2) ℝ i)) =
      -2 * (16 / (‖z‖ ^ 2 + 4) ^ 2) := by
  let q : LoopPlane → ℝ := fun x => Real.log (‖x‖ ^ 2 + 4)
  have hq : ContDiff ℝ ∞ q :=
    ((contDiff_norm_sq ℝ).add contDiff_const).log (by intro x; positivity)
  have heq : (fun x : LoopPlane => Real.log (16 / (‖x‖ ^ 2 + 4) ^ 2)) =
      (fun x => Real.log 16 - 2 * q x) := by
    funext x
    rw [Real.log_div (by norm_num) (by positivity), Real.log_pow]
    rfl
  have hfirst (x v : LoopPlane) :
      fderiv ℝ (fun x : LoopPlane => Real.log (16 / (‖x‖ ^ 2 + 4) ^ 2)) x v =
      -2 * fderiv ℝ q x v := by
    rw [heq, fderiv_const_sub, fderiv_const_mul (hq.differentiable (by simp) x)]
    simp only [neg_apply, smul_apply, smul_eq_mul]
    ring
  have hsecond (v : LoopPlane) :
      fderiv ℝ (fun y => fderiv ℝ
        (fun x : LoopPlane => Real.log (16 / (‖x‖ ^ 2 + 4) ^ 2)) y v) z v =
      -2 * (2 * ‖v‖ ^ 2 / (‖z‖ ^ 2 + 4) -
        4 * (inner ℝ z v) ^ 2 / (‖z‖ ^ 2 + 4) ^ 2) := by
    simp_rw [hfirst]
    have hd : DifferentiableAt ℝ (fun y => fderiv ℝ q y v) z :=
      ((hq.contDiffAt.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).differentiableAt
        (by simp)
    rw [fderiv_const_mul hd]
    simp only [smul_apply, smul_eq_mul]
    rw [M60.second_fderiv_log_norm_sq_add 4 (by norm_num)]
  rw [Fin.sum_univ_two, hsecond, hsecond]
  simp only [OrthonormalBasis.norm_eq_one, one_pow]
  have hs : (inner ℝ z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) ^ 2 +
      (inner ℝ z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) ^ 2 = ‖z‖ ^ 2 := by
    simpa only [Fin.sum_univ_two, real_inner_comm] using
      (EuclideanSpace.basisFun (Fin 2) ℝ).sum_sq_inner_right z
  have hden : ‖z‖ ^ 2 + 4 ≠ 0 := by positivity
  field_simp
  nlinarith

end PoincareConjecture
