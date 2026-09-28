import PoincareConjecture.Proofs.M47.BlowupControlsCapTensorAction

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M47

variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]

theorem cap_array_contraction_norm_le (T : ι → κ → ℝ) (S : κ → μ → ℝ) :
    ‖(WithLp.toLp 2 (fun p : ι × μ => ∑ k, T p.1 k * S k p.2) :
      EuclideanSpace ℝ (ι × μ))‖ ≤
      ‖(WithLp.toLp 2 (fun p : ι × κ => T p.1 p.2) : EuclideanSpace ℝ (ι × κ))‖ *
        ‖(WithLp.toLp 2 (fun p : κ × μ => S p.1 p.2) : EuclideanSpace ℝ (κ × μ))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [mul_pow, cap_array_norm_sq, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i, ∑ j, (∑ k, T i k ^ 2) * ∑ k, S k j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (T i) (fun k => S k j)
    _ = _ := by
      simp only [← Finset.mul_sum, ← Finset.sum_mul]
      congr 1
      exact Finset.sum_comm

theorem cap_array_triangle_abs_le (A : ι → κ → ℝ)
    (U : ι → μ → ℝ) (S : μ → κ → ℝ) :
    |∑ i, ∑ j, ∑ k, A i j * U i k * S k j| ≤
      ‖(WithLp.toLp 2 (fun p : ι × κ => A p.1 p.2) : EuclideanSpace ℝ (ι × κ))‖ *
        ‖(WithLp.toLp 2 (fun p : ι × μ => U p.1 p.2) : EuclideanSpace ℝ (ι × μ))‖ *
        ‖(WithLp.toLp 2 (fun p : μ × κ => S p.1 p.2) : EuclideanSpace ℝ (μ × κ))‖ := by
  have h := cap_array_pairing_abs_le (fun p : ι × κ => A p.1 p.2)
    (fun p : ι × κ => ∑ k, U p.1 k * S k p.2)
  simp only [Fintype.sum_prod_type, Finset.mul_sum, ← mul_assoc] at h
  refine h.trans ?_
  calc
    _ ≤ ‖(WithLp.toLp 2 (fun p : ι × κ => A p.1 p.2) : EuclideanSpace ℝ (ι × κ))‖ *
        (‖(WithLp.toLp 2 (fun p : ι × μ => U p.1 p.2) : EuclideanSpace ℝ (ι × μ))‖ *
        ‖(WithLp.toLp 2 (fun p : μ × κ => S p.1 p.2) : EuclideanSpace ℝ (μ × κ))‖) :=
      mul_le_mul_of_nonneg_left (cap_array_contraction_norm_le U S) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

theorem cap_array_linear_combination_norm_le (c : κ → ℝ) (T : κ → ι → ℝ) :
    ‖(WithLp.toLp 2 (fun i => ∑ k, c k * T k i) : EuclideanSpace ℝ ι)‖ ≤
      ‖(WithLp.toLp 2 c : EuclideanSpace ℝ κ)‖ *
        ‖(WithLp.toLp 2 (fun p : κ × ι => T p.1 p.2) : EuclideanSpace ℝ (κ × ι))‖ := by
  apply (sq_le_sq₀ (norm_nonneg _)
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  simp only [mul_pow, cap_array_norm_sq, Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i, (∑ k, c k ^ 2) * ∑ k, T k i ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c (fun k => T k i)
    _ = _ := by rw [← Finset.mul_sum, Finset.sum_comm]

end PoincareConjecture.M47
