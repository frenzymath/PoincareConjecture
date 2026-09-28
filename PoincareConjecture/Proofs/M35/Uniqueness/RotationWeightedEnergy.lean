import PoincareConjecture.Proofs.M35.Uniqueness.RotationDerivative









set_option autoImplicit false

noncomputable section

namespace PoincareConjecture.M35.Uniqueness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem linear_skew_inner_swap (B : V →L[ℝ] V)
    (hB : ∀ x, inner ℝ x (B x) = 0) (x y : V) :
    inner ℝ x (B y) = -inner ℝ (B x) y := by
  have h := hB (x + y)
  rw [map_add, inner_add_left, inner_add_right, inner_add_right,
    hB x, hB y, ← real_inner_comm y (B x)] at h
  linarith only [h]

theorem perpendicular_projection_norm_sq_le {n : V} (hn : ‖n‖ = 1) (v : V) :
    ‖v - (inner ℝ n v) • n‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  rw [norm_sub_sq_real, inner_smul_right, real_inner_comm v n,
    norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, hn]
  nlinarith only [sq_nonneg (inner ℝ n v)]

omit [InnerProductSpace ℝ V] in
private theorem norm_add_sq_le_twice (v w : V) :
    ‖v + w‖ ^ 2 ≤ 2 * ‖v‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (v + w)) (norm_add_le v w) 2
  nlinarith only [h, sq_nonneg (‖v‖ - ‖w‖)]




theorem rotation_weighted_energy_bound (B : V →L[ℝ] V)
    {n : V} (hn : ‖n‖ = 1) (y : V) {a b l p : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hl : a * l ^ 2 ≤ b) :
    a * ‖(l * p) • B n + (B y - (inner ℝ n (B y)) • n)‖ ^ 2 +
        b * ((a * l / b) * inner ℝ n (B y)) ^ 2 ≤
      3 * ‖B‖ ^ 2 * (b * p ^ 2 + a * ‖y‖ ^ 2) := by
  let q := inner ℝ n (B y)
  have hnB : ‖B n‖ ^ 2 ≤ ‖B‖ ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    simpa only [hn, mul_one] using B.le_opNorm n
  have hyB : ‖B y‖ ^ 2 ≤ ‖B‖ ^ 2 * ‖y‖ ^ 2 := by
    exact (pow_le_pow_left₀ (norm_nonneg _) (B.le_opNorm y) 2).trans_eq (mul_pow _ _ 2)
  have hq : q ^ 2 ≤ ‖B y‖ ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg (inner ℝ n (B y)))
      (abs_real_inner_le_norm n (B y)) 2
    simpa only [q, hn, one_mul, sq_abs] using h
  have hw : ‖B y - q • n‖ ^ 2 ≤ ‖B y‖ ^ 2 :=
    perpendicular_projection_norm_sq_le hn (B y)
  have ht : ‖(l * p) • B n + (B y - q • n)‖ ^ 2 ≤
      2 * l ^ 2 * p ^ 2 * ‖B n‖ ^ 2 + 2 * ‖B y‖ ^ 2 := by
    have h := norm_add_sq_le_twice ((l * p) • B n) (B y - q • n)
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_pow] at h
    nlinarith only [h, hw]
  have hr : b * ((a * l / b) * q) ^ 2 ≤ a * q ^ 2 := by
    calc
      _ = (a * q ^ 2 / b) * (a * l ^ 2) := by field_simp
      _ ≤ (a * q ^ 2 / b) * b := mul_le_mul_of_nonneg_left hl (by positivity)
      _ = a * q ^ 2 := div_mul_cancel₀ _ hb.ne'
  have hrad : a * l ^ 2 * p ^ 2 * ‖B n‖ ^ 2 ≤ b * p ^ 2 * ‖B‖ ^ 2 := by
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right hl (sq_nonneg p)) hnB (sq_nonneg _) (by positivity)
  change a * ‖(l * p) • B n + (B y - q • n)‖ ^ 2 +
    b * ((a * l / b) * q) ^ 2 ≤ _
  have ht' := mul_le_mul_of_nonneg_left ht ha.le
  have hq' := mul_le_mul_of_nonneg_left hq ha.le
  have hy' := mul_le_mul_of_nonneg_left hyB ha.le
  have hnonneg : 0 ≤ b * p ^ 2 * ‖B‖ ^ 2 := by positivity
  nlinarith only [ht', hq', hy', hr, hrad, hnonneg]

end PoincareConjecture.M35.Uniqueness
