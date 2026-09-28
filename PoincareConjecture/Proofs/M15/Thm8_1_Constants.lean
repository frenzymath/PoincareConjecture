import PoincareConjecture.Proofs.M15.Thm8_1_Reduction










set_option autoImplicit false

namespace PoincareConjecture.Proofs.M15



noncomputable def theorem81Kappa (n : ℕ) (epsilon0 lower : ℝ) : ℝ :=
  min (epsilon0 ^ n) (lower ^ 2 / 9)



theorem theorem81Kappa_pos {n : ℕ} {epsilon0 lower : ℝ}
    (hepsilon0 : 0 < epsilon0) (hlower : 0 < lower) :
    0 < theorem81Kappa n epsilon0 lower := by
  exact lt_min (pow_pos hepsilon0 _) (div_pos (sq_pos_of_pos hlower) (by norm_num))



theorem theorem81Kappa_le_ratio {n : ℕ} {epsilon0 lower epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon0) (hlower : 0 ≤ lower) (hepsilon : 0 < epsilon)
    (halternative : epsilon0 ≤ epsilon ∨
      lower ≤ 3 * Real.rpow epsilon ((n : ℝ) / 2)) :
    theorem81Kappa n epsilon0 lower ≤ epsilon ^ n := by
  rcases halternative with hlarge | hsmall
  · exact (min_le_left _ _).trans (pow_le_pow_left₀ hepsilon0 hlarge n)
  · have hsquare : (Real.rpow epsilon ((n : ℝ) / 2)) ^ 2 = epsilon ^ n := by
      calc
        (Real.rpow epsilon ((n : ℝ) / 2)) ^ 2 =
            Real.rpow epsilon ((n : ℝ) / 2 * 2) := by
          simp only [Real.rpow_eq_pow]
          rw [Real.rpow_mul hepsilon.le, Real.rpow_two]
        _ = epsilon ^ n := by
          simp only [Real.rpow_eq_pow]
          rw [div_mul_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0), Real.rpow_natCast]
    apply (min_le_right _ _).trans
    have hsq := mul_self_le_mul_self hlower hsmall
    nlinarith [hsquare]

end PoincareConjecture.Proofs.M15
