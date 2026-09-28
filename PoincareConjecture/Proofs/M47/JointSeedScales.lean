import PoincareConjecture.Proofs.M47.JointSeedLogarithmic

set_option autoImplicit false

namespace PoincareConjecture.M47

theorem jointSeed_worldline_scale_budget
    {A C c rho v : ℝ} (hA : 0 < A) (hC : 0 < C) (hrho : 0 < rho) (hv : 0 < v)
    (hc : c ≤ 1 / (4 * A * C)) (hsmall : v ≤ rho ^ 2 / (4 * A)) :
    0 < max (rho⁻¹ ^ 2) (C * c / v) ∧
      A * max (rho⁻¹ ^ 2) (C * c / v) * v ≤ 1 / 4 := by
  refine ⟨lt_of_lt_of_le (sq_pos_of_pos (inv_pos.mpr hrho)) (le_max_left _ _), ?_⟩
  rw [mul_max_of_nonneg _ _ hA.le, max_mul_of_nonneg _ _ hv.le, max_le_iff]
  constructor
  · have hbound := (le_div_iff₀ (by positivity : 0 < 4 * A)).1 hsmall
    have hidentity : A * rho⁻¹ ^ 2 * v = (A * v) / rho ^ 2 := by
      rw [div_eq_mul_inv, inv_pow]
      ring
    rw [hidentity]
    apply (div_le_iff₀ (sq_pos_of_pos hrho)).2
    nlinarith
  · have hbound := (le_div_iff₀ (by positivity : 0 < 4 * A * C)).1 hc
    have hidentity : A * (C * c / v) * v = A * C * c := by
      field_simp
    rw [hidentity]
    nlinarith

theorem jointSeed_worldline_uniform_scale
    {C c rho a v : ℝ} (hC : 0 ≤ C) (hc : 0 ≤ c) (ha : 0 < a) (hav : a ≤ v) :
    4 * max (rho⁻¹ ^ 2) (C * c / v) / 3 ≤
      2 * max (rho⁻¹ ^ 2) (C * c / a) := by
  have hquot : C * c / v ≤ C * c / a :=
    div_le_div_of_nonneg_left (mul_nonneg hC hc) ha hav
  have hmax := max_le_max (le_rfl (a := rho⁻¹ ^ 2)) hquot
  have hnonneg : 0 ≤ max (rho⁻¹ ^ 2) (C * c / a) :=
    (sq_nonneg _).trans (le_max_left _ _)
  linarith

theorem jointSeed_terminal_below_scale
    {C c rho v R : ℝ} (hC : 1 ≤ C) (hv : 0 < v) (hR : 0 ≤ R)
    (hjoint : v * R ≤ c) :
    R ≤ max (rho⁻¹ ^ 2) (C * c / v) ∧
      C * R ≤ max (rho⁻¹ ^ 2) (C * c / v) := by
  have hCpos : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 1).trans hC
  have hupper : R ≤ c / v := (le_div_iff₀ hv).2 (by simpa only [mul_comm] using hjoint)
  have hbound : C * R ≤ C * c / v := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hupper hCpos
  have hclipped := hbound.trans (le_max_right (rho⁻¹ ^ 2) _)
  refine ⟨?_, hclipped⟩
  have hRCR : R ≤ C * R := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hR
  exact hRCR.trans hclipped

end PoincareConjecture.M47
