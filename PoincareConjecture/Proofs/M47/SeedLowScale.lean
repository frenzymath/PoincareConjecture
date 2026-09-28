import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallTestScale

set_option autoImplicit false

namespace PoincareConjecture.M47

theorem exists_seed_low_scalar_scale (C threshold : ℝ) {rNext : ℝ}
    (hrNext : 0 < rNext) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ rNext ∧ 128 ≤ r0⁻¹ ^ 2 ∧
      threshold ≤ r0⁻¹ ^ 2 ∧ rNext⁻¹ ^ 2 ≤ r0⁻¹ ^ 2 ∧
      (C / 6) * rNext⁻¹ ^ 2 ≤ r0⁻¹ ^ 2 ∧ r0 ^ 2 ≤ 1 / 128 := by
  let Q := max 128 (max threshold (max (rNext⁻¹ ^ 2) ((C / 6) * rNext⁻¹ ^ 2)))
  have h128 : (128 : ℝ) ≤ Q := le_max_left _ _
  have hQ : 0 < Q := lt_of_lt_of_le (by norm_num) h128
  have hthreshold : threshold ≤ Q := (le_max_left _ _).trans (le_max_right _ _)
  have hrQ : rNext⁻¹ ^ 2 ≤ Q :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCQ : (C / 6) * rNext⁻¹ ^ 2 ≤ Q :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  let r0 := (Real.sqrt Q)⁻¹
  have hr0 : 0 < r0 := inv_pos.mpr (Real.sqrt_pos.mpr hQ)
  have hinv : r0⁻¹ ^ 2 = Q := by
    simp only [r0, inv_inv, Real.sq_sqrt hQ.le]
  have hle : r0 ≤ rNext := by
    have hi : rNext⁻¹ ≤ r0⁻¹ := by
      rw [← hinv] at hrQ
      nlinarith only [hrQ, inv_pos.mpr hrNext, inv_pos.mpr hr0]
    exact (inv_le_inv₀ hrNext hr0).mp hi
  have hsquare : r0 ^ 2 = 1 / Q := by
    rw [← hinv]
    field_simp
  refine ⟨r0, hr0, hle, hinv ▸ h128, hinv ▸ hthreshold,
    hinv ▸ hrQ, hinv ▸ hCQ, ?_⟩
  rw [hsquare]
  exact one_div_le_one_div_of_le (by norm_num) h128

end PoincareConjecture.M47
