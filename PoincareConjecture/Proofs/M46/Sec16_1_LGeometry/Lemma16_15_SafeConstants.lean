import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_BarrierConstants










set_option autoImplicit false

namespace PoincareConjecture.Proofs.M46




theorem exists_initialSafeDuration {rho budget : ℝ} (hrho : 0 < rho)
    (hbudget : 0 ≤ budget) :
    ∃ a : ℝ, 0 < a ∧ a ≤ rho ^ 2 / 12 ∧ a ≤ rho ^ 2 / 4 ∧
      budget < rho ^ 2 / (16 * Real.sqrt a) := by
  let q := rho ^ 2 / (32 * (budget + 1))
  have hq : 0 < q := by dsimp only [q]; positivity
  let a := min (rho ^ 2 / 24) (q ^ 2)
  have ha : 0 < a := lt_min (by positivity) (sq_pos_of_pos hq)
  have hsmall : a ≤ rho ^ 2 / 24 := min_le_left _ _
  have hroot : Real.sqrt a ≤ q := Real.sqrt_le_iff.mpr ⟨hq.le, min_le_right _ _⟩
  have hfactor := mul_le_mul_of_nonneg_left hroot
    (by positivity : 0 ≤ 16 * (budget + 1))
  have hcancel : 16 * (budget + 1) * q = rho ^ 2 / 2 := by
    dsimp only [q]
    field_simp [show budget + 1 ≠ 0 by positivity]
    ring
  rw [hcancel] at hfactor
  refine ⟨a, ha, by nlinarith [sq_nonneg rho], by nlinarith [sq_nonneg rho], ?_⟩
  apply (lt_div_iff₀ (mul_pos (by norm_num) (Real.sqrt_pos.mpr ha))).mpr
  nlinarith [Real.sqrt_pos.mpr ha, sq_pos_of_pos hrho]





theorem exists_metricCapSideRadius {mu : ℝ} (hmu : 0 < mu) (ell lowerRadius : ℝ) :
    ∃ A : ℝ, 0 < A ∧ lowerRadius < A / 2 ∧ ell < mu * A ^ 2 / 4 := by
  let q := (max ell 0 + 1) / mu
  have hq : 0 < q := by dsimp only [q]; positivity
  let A := max (2 * lowerRadius + 2) (4 * Real.sqrt q)
  have hA : 0 < A :=
    (by positivity : 0 < 4 * Real.sqrt q).trans_le (le_max_right _ _)
  have hlarge : 4 * Real.sqrt q ≤ A := le_max_right _ _
  have hsquare : 16 * q ≤ A ^ 2 := by
    nlinarith [Real.sq_sqrt hq.le, Real.sqrt_nonneg q]
  have hscale := mul_le_mul_of_nonneg_left hsquare hmu.le
  have hcancel : mu * q = max ell 0 + 1 := by
    dsimp only [q]
    exact mul_div_cancel₀ _ hmu.ne'
  have hbudget : ell < max ell 0 + 1 := (le_max_left ell 0).trans_lt (lt_add_one _)
  refine ⟨A, hA, by linarith [le_max_left (2 * lowerRadius + 2) (4 * Real.sqrt q)], ?_⟩
  nlinarith [le_max_right ell 0]

end PoincareConjecture.Proofs.M46
