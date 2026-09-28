import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false

namespace PoincareConjecture.SingularRegularLimit

theorem exists_uniform_inverse_square_margin {c L : ℝ} (hc : 1 < c) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ L →
      r⁻¹ ^ 2 + δ ≤ (r / c)⁻¹ ^ 2 ∧ (c * r)⁻¹ ^ 2 ≤ r⁻¹ ^ 2 - δ := by
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcinv : 0 < c⁻¹ := inv_pos.mpr hcpos
  have hcinv1 : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  have hleft : 0 < c ^ 2 - 1 := by nlinarith
  have hright : 0 < 1 - c⁻¹ ^ 2 := by nlinarith
  have hqL : 0 < L⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hL)
  let δ := min ((c ^ 2 - 1) * L⁻¹ ^ 2) ((1 - c⁻¹ ^ 2) * L⁻¹ ^ 2) / 2
  have hδ : 0 < δ := half_pos (lt_min (mul_pos hleft hqL) (mul_pos hright hqL))
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrL
  have hInv : L⁻¹ ≤ r⁻¹ := (inv_le_inv₀ hL hr).mpr hrL
  have hq : L⁻¹ ^ 2 ≤ r⁻¹ ^ 2 := by
    nlinarith [inv_pos.mpr hL, inv_pos.mpr hr]
  have hδle : δ ≤ min ((c ^ 2 - 1) * L⁻¹ ^ 2) ((1 - c⁻¹ ^ 2) * L⁻¹ ^ 2) := by
    exact half_le_self (le_of_lt (lt_min (mul_pos hleft hqL) (mul_pos hright hqL)))
  have hδleft := ((hδle.trans (min_le_left _ _)).trans
    (mul_le_mul_of_nonneg_left hq hleft.le))
  have hδright := ((hδle.trans (min_le_right _ _)).trans
    (mul_le_mul_of_nonneg_left hq hright.le))
  have hsmall : (r / c)⁻¹ ^ 2 = c ^ 2 * r⁻¹ ^ 2 := by
    simp only [div_eq_mul_inv, mul_inv_rev, inv_inv, mul_pow]
  have hlarge : (c * r)⁻¹ ^ 2 = c⁻¹ ^ 2 * r⁻¹ ^ 2 := by
    rw [mul_inv_rev, mul_pow, mul_comm]
  rw [hsmall, hlarge]
  constructor <;> nlinarith

end PoincareConjecture.SingularRegularLimit
