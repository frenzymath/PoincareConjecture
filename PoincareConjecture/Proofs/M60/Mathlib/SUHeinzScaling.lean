import PoincareConjecture.Proofs.M60.Mathlib.SUNonnegativeHeinz
import Mathlib.Analysis.Normed.Module.Ball.Pointwise
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped ContDiff Pointwise

namespace PoincareConjecture.M60

theorem fderiv_comp_homothety {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} (R : ℝ) (x : E) (hu : DifferentiableAt ℝ u (R • x)) :
    fderiv ℝ (fun y => u (R • y)) x = R • fderiv ℝ u (R • x) := by
  have h := (hu.hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul R)).fderiv
  dsimp only [Function.comp_def] at h
  rw [h]
  ext w
  simp only [ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply,
    map_smul]

theorem suPlaneLaplacian_rescale {u : EuclideanSpace ℝ (Fin 2) → ℝ}
    (hu : ContDiff ℝ ∞ u) (R : ℝ) (x : EuclideanSpace ℝ (Fin 2)) :
    suPlaneLaplacian (fun y => R ^ 2 * u (R • y)) x =
      R ^ 4 * suPlaneLaplacian u (R • x) := by
  have hcomp : ContDiff ℝ ∞ (fun y => u (R • y)) := hu.comp (contDiff_id.const_smul R)
  have hd (y : EuclideanSpace ℝ (Fin 2)) :
      fderiv ℝ (fun z => R ^ 2 * u (R • z)) y = R ^ 3 • fderiv ℝ u (R • y) := by
    rw [fderiv_const_mul (hcomp.differentiable (by simp) y),
      fderiv_comp_homothety R y (hu.differentiable (by simp) _), smul_smul]
    congr 1
  have hdu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hduc : ContDiff ℝ ∞ (fun y => fderiv ℝ u (R • y)) :=
    hdu.comp (contDiff_id.const_smul R)
  unfold suPlaneLaplacian
  rw [show fderiv ℝ (fun y => R ^ 2 * u (R • y)) =
    (fun y => R ^ 3 • fderiv ℝ u (R • y)) from funext hd,
    fderiv_fun_const_smul (hduc.differentiable (by simp) x),
    fderiv_comp_homothety R x (hdu.differentiable (by simp) _), smul_smul]
  simp only [smul_apply, smul_eq_mul, ← Finset.mul_sum]
  congr 1

theorem suIntegral_rescale (u : EuclideanSpace ℝ (Fin 2) → ℝ) {R : ℝ} (hR : 0 < R) :
    (∫ x in Metric.closedBall 0 1, R ^ 2 * u (R • x)) =
      ∫ x in Metric.closedBall 0 R, u x := by
  have hball : R • Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 =
      Metric.closedBall 0 R := by
    rw [smul_closedBall' hR.ne', smul_zero, Real.norm_eq_abs, abs_of_pos hR, mul_one]
  rw [integral_const_mul, Measure.setIntegral_comp_smul_of_pos volume u _ hR,
    finrank_euclideanSpace_fin, hball, smul_eq_mul]
  field_simp

theorem exists_heinz_estimate_all_radii :
    ∃ A : ℝ, 0 < A ∧ ∀ (K R : ℝ), 0 ≤ K → 0 < R →
      ∀ u : EuclideanSpace ℝ (Fin 2) → ℝ,
        ContDiff ℝ ∞ u → (∀ x, 0 ≤ u x) →
        (∀ x ∈ Metric.ball 0 R, -K * (u x) ^ 2 ≤ suPlaneLaplacian u x) →
        A * K * (∫ x in Metric.closedBall 0 R, u x) ≤ 1 →
        R ^ 2 * u 0 ≤ A * (∫ x in Metric.closedBall 0 R, u x) := by
  obtain ⟨A, hA, hest⟩ := exists_heinz_estimate
  refine ⟨A, hA, fun K R hK hR u hu hnonneg hlap hsmall => ?_⟩
  let v : EuclideanSpace ℝ (Fin 2) → ℝ := fun x => R ^ 2 * u (R • x)
  have hv : ContDiff ℝ ∞ v := contDiff_const.mul (hu.comp (contDiff_id.const_smul R))
  have hvlap (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ Metric.ball 0 1) :
      -K * (v x) ^ 2 ≤ suPlaneLaplacian v x := by
    have hxR : R • x ∈ Metric.ball 0 R := by
      simp only [Metric.mem_ball, dist_zero_right] at hx ⊢
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
      nlinarith only [hx, hR]
    have hm := mul_le_mul_of_nonneg_left (hlap (R • x) hxR) (pow_nonneg hR.le 4)
    rw [suPlaneLaplacian_rescale hu]
    dsimp only [v]
    nlinarith only [hm]
  have hm := hest K 1 hK (by norm_num) le_rfl v hv
    (fun x => mul_nonneg (sq_nonneg R) (hnonneg _)) hvlap
    (by simpa only [v, suIntegral_rescale u hR] using hsmall)
  simpa only [v, one_pow, one_mul, smul_zero, suIntegral_rescale u hR] using hm

end PoincareConjecture.M60
