import PoincareConjecture.Proofs.M35.Sec12_4_Uniqueness.RadialMapJets









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff

namespace PoincareConjecture.M35.Uniqueness

private noncomputable abbrev e (i : Fin 3) : StandardCapSpace := EuclideanSpace.single i 1

variable {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {r : ℝ} (hr : 0 < r)

include hr

theorem radialScaleMap_axis : radialScaleMap h (r • e 2) = (r * h r) • e 2 := by
  simp only [radialScaleMap, _root_.norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  have hn : ‖e 2‖ = 1 := by simp [e]
  rw [hn, mul_one, smul_smul, mul_comm]

include hh

theorem radialScaleMap_fderiv_angular (i : Fin 3) (hi : i ≠ 2) :
    fderiv ℝ (radialScaleMap h) (r • e 2) (e i) = h r • e i := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e i) = 0 := by
    fin_cases i <;> simp_all [e, EuclideanSpace.inner_single_left, inner_smul_left]
  rw [radialScaleMap_fderiv hh hx, hn, hxe, mul_zero, zero_smul, add_zero]

theorem radialScaleMap_fderiv_axis :
    fderiv ℝ (radialScaleMap h) (r • e 2) (e 2) =
      (h r + r * deriv h r) • e 2 := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e 2) = r := by simp [e, inner_smul_left]
  rw [radialScaleMap_fderiv hh hx, hn, hxe, div_mul_cancel₀ _ hr.ne',
    smul_smul, ← add_smul, mul_comm (deriv h r) r]

theorem radialScaleMap_hessian_angular (he : Function.Even h) (i : Fin 3) (hi : i ≠ 2) :
    fderiv ℝ (fderiv ℝ (radialScaleMap h)) (r • e 2) (e i) (e i) =
      deriv h r • e 2 := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e i) = 0 := by
    fin_cases i <;> simp_all [e, EuclideanSpace.inner_single_left, inner_smul_left]
  have hei : inner ℝ (e i) (e i) = 1 := by simp [e]
  rw [radialScaleMap_hessian hh he hx, hn, hxe, hei]
  simp only [mul_zero, zero_smul, zero_add, mul_one, add_zero, smul_smul]
  rw [div_mul_cancel₀ _ hr.ne']

theorem radialScaleMap_hessian_axis (he : Function.Even h) :
    fderiv ℝ (fderiv ℝ (radialScaleMap h)) (r • e 2) (e 2) (e 2) =
      (2 * deriv h r + r * deriv (deriv h) r) • e 2 := by
  have hx : r • e 2 ≠ 0 := smul_ne_zero hr.ne' (by simp [e])
  have hn : ‖r • e 2‖ = r := by simp [e, _root_.norm_smul, abs_of_pos hr]
  have hxe : inner ℝ (r • e 2) (e 2) = r := by simp [e, inner_smul_left]
  have hei : inner ℝ (e 2) (e 2) = 1 := by simp [e]
  rw [radialScaleMap_hessian hh he hx, hn, hxe, hei]
  simp only [smul_smul, ← add_smul]
  congr 1
  field_simp [hr.ne']
  ring

end PoincareConjecture.M35.Uniqueness
