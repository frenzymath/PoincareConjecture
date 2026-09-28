import Mathlib.Analysis.InnerProductSpace.Basic








set_option autoImplicit false

open scoped InnerProductSpace

namespace Poincare.InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


theorem norm_add_sq_le_of_almost_opposite (v z : E) {η δ τ : ℝ}
    (hv : ‖v‖ ≤ 1) (hz : ‖z‖ ≤ 1 + η)
    (hpair : ⟪z, v⟫_ℝ ≤ -1 + 2 * δ + τ) :
    ‖z + v‖ ^ 2 ≤ 2 * η + η ^ 2 + 4 * δ + 2 * τ := by
  have hv2 := (sq_le_sq₀ (norm_nonneg v) zero_le_one).mpr hv
  have hz2 := (sq_le_sq₀ (norm_nonneg z) ((norm_nonneg z).trans hz)).mpr hz
  rw [norm_add_sq_real]
  nlinarith


theorem norm_add_le_sqrt_of_almost_opposite (v z : E) {η δ τ : ℝ}
    (hv : ‖v‖ ≤ 1) (hz : ‖z‖ ≤ 1 + η)
    (hpair : ⟪z, v⟫_ℝ ≤ -1 + 2 * δ + τ) :
    ‖z + v‖ ≤ Real.sqrt (2 * η + η ^ 2 + 4 * δ + 2 * τ) :=
  Real.le_sqrt_of_sq_le (norm_add_sq_le_of_almost_opposite v z hv hz hpair)



theorem abs_inner_le_of_almost_opposite (v z w : E) {δ q : ℝ}
    (hw : ‖w‖ ≤ 1) (hcross : |⟪v, w⟫_ℝ| ≤ δ) (hz : ‖z + v‖ ≤ q) :
    |⟪z, w⟫_ℝ| ≤ δ + q := by
  have herr : |⟪z + v, w⟫_ℝ| ≤ q := by
    apply (abs_real_inner_le_norm (z + v) w).trans
    calc
      ‖z + v‖ * ‖w‖ ≤ ‖z + v‖ * 1 :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ ≤ q := by simpa only [mul_one] using hz
  calc
    |⟪z, w⟫_ℝ| = |⟪z + v, w⟫_ℝ - ⟪v, w⟫_ℝ| := by
      rw [inner_add_left, add_sub_cancel_right]
    _ ≤ |⟪z + v, w⟫_ℝ| + |⟪v, w⟫_ℝ| := abs_sub _ _
    _ ≤ q + δ := add_le_add herr hcross
    _ = δ + q := add_comm _ _


theorem abs_inner_le_of_almost_opposite_pair (v w z z' : E) {δ q r : ℝ}
    (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) (hcross : |⟪v, w⟫_ℝ| ≤ δ)
    (hz : ‖z + v‖ ≤ q) (hz' : ‖z' + w‖ ≤ r) :
    |⟪z, z'⟫_ℝ| ≤ δ + q + r + q * r := by
  have hzw := abs_inner_le_of_almost_opposite v z w hw hcross hz
  have hznorm : ‖z‖ ≤ 1 + q := by
    calc
      ‖z‖ = ‖(z + v) - v‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖z + v‖ + ‖v‖ := norm_sub_le _ _
      _ ≤ q + 1 := add_le_add hz hv
      _ = 1 + q := add_comm _ _
  have herr : |⟪z, z' + w⟫_ℝ| ≤ (1 + q) * r :=
    (abs_real_inner_le_norm z (z' + w)).trans
      (mul_le_mul hznorm hz' (norm_nonneg _) ((norm_nonneg z).trans hznorm))
  calc
    |⟪z, z'⟫_ℝ| = |⟪z, z' + w⟫_ℝ - ⟪z, w⟫_ℝ| := by
      rw [inner_add_right, add_sub_cancel_right]
    _ ≤ |⟪z, z' + w⟫_ℝ| + |⟪z, w⟫_ℝ| := abs_sub _ _
    _ ≤ (1 + q) * r + (δ + q) := add_le_add herr hzw
    _ = δ + q + r + q * r := by ring


theorem family_cross_bounds_of_almost_opposite {ι : Type*}
    (v z : ι → E) {δ q : ℝ}
    (hv : ∀ i, ‖v i‖ ≤ 1)
    (hcross : ∀ i j, i ≠ j → |⟪v i, v j⟫_ℝ| ≤ δ)
    (hz : ∀ i, ‖z i + v i‖ ≤ q) :
    (∀ i j, i ≠ j → |⟪z i, v j⟫_ℝ| ≤ δ + q) ∧
      (∀ i j, i ≠ j → |⟪z i, z j⟫_ℝ| ≤ δ + 2 * q + q ^ 2) := by
  constructor
  · exact fun i j hij => abs_inner_le_of_almost_opposite
      (v i) (z i) (v j) (hv j) (hcross i j hij) (hz i)
  · intro i j hij
    have h := abs_inner_le_of_almost_opposite_pair
      (v i) (v j) (z i) (z j) (hv i) (hv j) (hcross i j hij) (hz i) (hz j)
    nlinarith

end Poincare.InnerProductSpace
