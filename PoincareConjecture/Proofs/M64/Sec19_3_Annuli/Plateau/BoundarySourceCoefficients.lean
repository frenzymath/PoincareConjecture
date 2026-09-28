import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundarySourceVariations
import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64HorizontalSourceInverse_tendsto
    (tau : ℝ → ℝ ≃ₜ ℝ) (theta : ℝ → ℝ) {C : ℝ}
    (hC : ∀ x, |theta x| ≤ C)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x) (x : ℝ) :
    Tendsto (fun t => (tau t).symm x) (𝓝 0) (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using (continuous_abs.tendsto (0 : ℝ)).mul_const C)
  filter_upwards [hvar] with t ht
  have hid := ht ((tau t).symm x)
  rw [Homeomorph.apply_symm_apply] at hid
  have heq : (tau t).symm x - x = -(t * theta ((tau t).symm x)) := by linarith
  rw [Real.norm_eq_abs, heq, abs_neg, abs_mul]
  exact mul_le_mul_of_nonneg_left (hC _) (abs_nonneg t)

theorem m64HorizontalSource_coefficient_deriv
    (tau : ℝ → ℝ ≃ₜ ℝ) {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    {C : ℝ} (hC : ∀ x, |theta x| ≤ C)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x) (x : ℝ) :
    HasDerivAt (fun t => 1 + t * deriv theta ((tau t).symm x)) (deriv theta x) 0 := by
  have hinv := m64HorizontalSourceInverse_tendsto tau theta hC hvar x
  have hd := (htheta.continuous_deriv (by simp)).continuousAt.tendsto.comp hinv
  apply hasDerivAt_iff_tendsto_slope.mpr
  apply (hd.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := ht
  simp only [slope, zero_mul, add_zero, sub_zero, vsub_eq_sub, add_sub_cancel_left,
    smul_eq_mul, Function.comp_apply]
  rw [← mul_assoc, inv_mul_cancel₀ ht0, one_mul]

theorem m64HorizontalSource_inverse_coefficient_deriv
    (tau : ℝ → ℝ ≃ₜ ℝ) {theta : ℝ → ℝ} (htheta : ContDiff ℝ 1 theta)
    {C : ℝ} (hC : ∀ x, |theta x| ≤ C)
    (hvar : ∀ᶠ t : ℝ in 𝓝 0, ∀ x, tau t x = x + t * theta x) (x : ℝ) :
    HasDerivAt (fun t => (1 + t * deriv theta ((tau t).symm x))⁻¹)
      (-deriv theta x) 0 := by
  simpa only [Pi.inv_apply, zero_mul, add_zero, one_pow, div_one] using!
    (m64HorizontalSource_coefficient_deriv tau htheta hC hvar x).inv
    (by simp : (1 + (0 : ℝ) * deriv theta ((tau 0).symm x)) ≠ 0)

end PoincareConjecture
