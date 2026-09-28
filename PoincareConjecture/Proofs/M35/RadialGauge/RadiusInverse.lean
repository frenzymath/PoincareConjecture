import PoincareConjecture.Proofs.M35.RadialGauge.RadiusBounds
import PoincareConjecture.Proofs.M07.Analysis.Calculus.Diffeomorphism.Perturbation










set_option autoImplicit false

open scoped ContDiff NNReal

namespace PoincareConjecture.M35.RadialGauge

theorem mapRadius_deriv_sub_one_bound {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (r : ℝ)
    (hv : (1 + |r|) * |u r| ≤ 1 / 8)
    (hd : (1 + |r|) * |deriv u r| ≤ 1 / 8) :
    |deriv (mapRadius u) r - 1| ≤ 1 / 2 := by
  have hv' : |u r| ≤ 1 / 8 := by
    nlinarith only [hv, mul_nonneg (abs_nonneg r) (abs_nonneg (u r))]
  have he : |Real.exp (u r) - 1| ≤ 1 / 4 :=
    (Real.abs_exp_sub_one_le (by linarith)).trans (by linarith)
  have he2 : Real.exp (u r) ≤ 2 := by
    linarith only [he, le_abs_self (Real.exp (u r) - 1)]
  have hrdu : |r| * |deriv u r| ≤ 1 / 8 := by
    nlinarith only [hd, abs_nonneg (deriv u r)]
  have hprod := mul_le_mul he2 hrdu (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (show (0 : ℝ) ≤ 2 by norm_num)
  rw [(mapRadius_hasDerivAt ((hu.differentiable (by simp) r).hasDerivAt)).deriv]
  have heq : Real.exp (u r) * (1 + r * deriv u r) - 1 =
      (Real.exp (u r) - 1) + Real.exp (u r) * r * deriv u r := by ring
  rw [heq]
  have h := abs_add_le (Real.exp (u r) - 1) (Real.exp (u r) * r * deriv u r)
  rw [abs_mul, abs_mul, Real.abs_exp] at h
  nlinarith only [h, he, hprod]



theorem exists_mapRadius_smooth_inverse {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ∀ r, (1 + |r|) * |u r| ≤ 1 / 8)
    (hd : ∀ r, (1 + |r|) * |deriv u r| ≤ 1 / 8) :
    ∃ q : ℝ → ℝ, ContDiff ℝ ∞ q ∧
      (∀ r, q (mapRadius u r) = r) ∧ (∀ r, mapRadius u (q r) = r) := by
  have hs : ContDiff ℝ ∞ (mapRadius u) := contDiff_id.mul hu.exp
  have hclose (r : ℝ) : ‖fderiv ℝ (mapRadius u) r -
      ContinuousLinearMap.id ℝ ℝ‖ ≤ 1 / 2 := by
    have hderiv := ((mapRadius_hasDerivAt
      ((hu.differentiable (by simp) r).hasDerivAt)).sub (hasDerivAt_id r)).deriv
    have hdiff : deriv (fun s => mapRadius u s - s) r = deriv (mapRadius u) r - 1 := by
      change deriv (mapRadius u - id) r = _
      rw [hderiv, (mapRadius_hasDerivAt ((hu.differentiable (by simp) r).hasDerivAt)).deriv]
    have hnorm : ‖fderiv ℝ (mapRadius u) r - ContinuousLinearMap.id ℝ ℝ‖ =
        |deriv (mapRadius u) r - 1| := by
      rw [← fderiv_id (x := r)]
      rw [← fderiv_fun_sub (hs.differentiable (by simp) r) differentiableAt_id]
      rw [← norm_deriv_eq_norm_fderiv]
      change ‖deriv (fun s => mapRadius u s - s) r‖ = _
      rw [hdiff, Real.norm_eq_abs]
    rw [hnorm]
    exact mapRadius_deriv_sub_one_bound hu r (hv r) (hd r)
  obtain ⟨e, he, _, hei⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id
      hs (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  refine ⟨e.symm, hei, fun r => ?_, fun r => ?_⟩
  · rw [← he]
    exact e.symm_apply_apply r
  · rw [← he]
    exact e.apply_symm_apply r

end PoincareConjecture.M35.RadialGauge
