import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchCauchyKernel











noncomputable section

set_option autoImplicit false

open Set Complex Metric
open scoped Topology

namespace PoincareConjecture.M65Branch



def regularizedCauchyKernel (δ : ℝ) (z : ℂ) : ℂ :=
  star z / ((max (‖z‖ ^ 2) (δ ^ 2) : ℝ) : ℂ)



theorem norm_regularizedCauchyKernel {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖regularizedCauchyKernel δ z‖ = ‖z‖ / max (‖z‖ ^ 2) (δ ^ 2) := by
  have hm : 0 < max (‖z‖ ^ 2) (δ ^ 2) := (sq_pos_of_pos hδ).trans_le (le_max_right _ _)
  simp only [regularizedCauchyKernel, norm_div, norm_star, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hm]



theorem continuous_regularizedCauchyKernel {δ : ℝ} (hδ : 0 < δ) :
    Continuous (regularizedCauchyKernel δ) := by
  apply continuous_star.div
    (Complex.continuous_ofReal.comp ((continuous_norm.pow 2).max continuous_const))
  intro z
  apply Complex.ofReal_ne_zero.mpr
  exact ne_of_gt ((sq_pos_of_pos hδ).trans_le (le_max_right _ _))



theorem norm_regularizedCauchyKernel_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖regularizedCauchyKernel δ z‖ ≤ δ⁻¹ := by
  rw [norm_regularizedCauchyKernel hδ]
  have hm : 0 < max (‖z‖ ^ 2) (δ ^ 2) := (sq_pos_of_pos hδ).trans_le (le_max_right _ _)
  apply (div_le_iff₀ hm).mpr
  rw [inv_mul_eq_div]
  apply (le_div_iff₀ hδ).mpr
  rcases le_total ‖z‖ δ with h | h
  · exact (mul_le_mul_of_nonneg_right h hδ.le).trans (by
      nlinarith [le_max_right (‖z‖ ^ 2) (δ ^ 2)])
  · exact (mul_le_mul_of_nonneg_left h (norm_nonneg z)).trans (by
      nlinarith [le_max_left (‖z‖ ^ 2) (δ ^ 2)])




theorem norm_regularizedCauchyKernel_le_inv {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖regularizedCauchyKernel δ z‖ ≤ ‖z‖⁻¹ := by
  by_cases hz : z = 0
  · simp [hz, regularizedCauchyKernel]
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_regularizedCauchyKernel hδ]
  calc
    _ ≤ ‖z‖ / ‖z‖ ^ 2 := div_le_div_of_nonneg_left (norm_nonneg z)
      (sq_pos_of_pos hr) (le_max_left _ _)
    _ = ‖z‖⁻¹ := by field_simp



theorem regularizedCauchyKernel_eq_inv {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : δ ≤ ‖z‖) : regularizedCauchyKernel δ z = z⁻¹ := by
  have hsq : δ ^ 2 ≤ ‖z‖ ^ 2 := (sq_le_sq₀ hδ.le (norm_nonneg z)).mpr hz
  rw [regularizedCauchyKernel, max_eq_left hsq, Complex.inv_def z,
    Complex.normSq_eq_norm_sq, Complex.ofReal_inv]
  rfl




theorem norm_sub_regularizedCauchyKernel_le {δ : ℝ} (hδ : 0 < δ) (z : ℂ) :
    ‖z⁻¹ - regularizedCauchyKernel δ z‖ ≤
      (ball (0 : ℂ) δ).indicator (fun w => 2 * ‖w‖⁻¹) z := by
  by_cases hz : z ∈ ball (0 : ℂ) δ
  · rw [indicator_of_mem hz]
    calc
      _ ≤ ‖z⁻¹‖ + ‖regularizedCauchyKernel δ z‖ := norm_sub_le _ _
      _ ≤ ‖z‖⁻¹ + ‖z‖⁻¹ := add_le_add (le_of_eq (norm_inv _))
        (norm_regularizedCauchyKernel_le_inv hδ z)
      _ = _ := by ring
  · have hr : δ ≤ ‖z‖ := le_of_not_gt (fun h => hz (mem_ball_zero_iff.mpr h))
    rw [regularizedCauchyKernel_eq_inv hδ hr, sub_self, norm_zero, indicator_of_notMem hz]

end PoincareConjecture.M65Branch
