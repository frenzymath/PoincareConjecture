import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.ScalarComparison
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace











noncomputable section
set_option autoImplicit false

open Set
open scoped BigOperators

namespace PoincareConjecture.RiemannianMetric



theorem sum_sq_diagonal_le_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι ℝ} (hS : S.IsSymm) :
    (∑ i, S i i ^ 2) ≤ (S * S).trace := by
  classical
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  apply Finset.sum_le_sum
  intro i hi
  have hs : ∀ j, S i j * S j i = S i j ^ 2 := by
    intro j
    rw [hS.apply i j, pow_two]
  simp only [hs]
  exact Finset.single_le_sum (fun j hj => sq_nonneg (S i j)) (Finset.mem_univ i)



theorem sq_trace_le_card_mul_trace_mul_self {ι : Type*} [Fintype ι]
    {S : Matrix ι ι ℝ} (hS : S.IsSymm) :
    S.trace ^ 2 ≤ (Fintype.card ι : ℝ) * (S * S).trace := by
  have hdiag : S.trace ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, S i i ^ 2 := by
    simpa only [Matrix.trace, Matrix.diag, Finset.card_univ] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => S i i))
  exact hdiag.trans (mul_le_mul_of_nonneg_left
    (sum_sq_diagonal_le_trace_mul_self hS) (Nat.cast_nonneg _))



theorem trace_riccati_inequality {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) {S : Matrix ι ι ℝ} (hS : S.IsSymm)
    {h' ric κ : ℝ}
    (hode : h' = -(S * S).trace - ric)
    (hric : -(Fintype.card ι : ℝ) * κ ≤ ric) :
    h' + S.trace ^ 2 / (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) * κ := by
  have hm' : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr hm
  have htrace : S.trace ^ 2 / (Fintype.card ι : ℝ) ≤ (S * S).trace := by
    apply (div_le_iff₀ hm').mpr
    simpa only [mul_comm] using sq_trace_le_card_mul_trace_mul_self hS
  linarith


theorem trace_riccati_inequality_of_matrix_equation {ι : Type*} [Fintype ι]
    (hm : 0 < Fintype.card ι) {S S' K : Matrix ι ι ℝ} (hS : S.IsSymm)
    {κ : ℝ} (hode : S' = -(S * S) - K)
    (hric : -(Fintype.card ι : ℝ) * κ ≤ K.trace) :
    S'.trace + S.trace ^ 2 / (Fintype.card ι : ℝ) ≤ (Fintype.card ι : ℝ) * κ := by
  apply trace_riccati_inequality hm hS (ric := K.trace) _ hric
  simp only [hode, Matrix.trace_sub, Matrix.trace_neg]



theorem density_root_second_derivative_le {m h h' y y'' κ : ℝ}
    (hm : 0 < m) (hy : 0 ≤ y)
    (hriccati : h' + h ^ 2 / m ≤ m * κ)
    (hy'' : y'' = (h' / m + (h / m) ^ 2) * y) :
    y'' ≤ κ * y := by
  have hcoef : h' / m + (h / m) ^ 2 ≤ κ := by
    have heq : h' / m + (h / m) ^ 2 = (h' + h ^ 2 / m) / m := by
      field_simp
    rw [heq]
    exact (div_le_iff₀ hm).mpr (by simpa only [mul_comm] using hriccati)
  rw [hy'']
  exact mul_le_mul_of_nonneg_right hcoef hy

end PoincareConjecture.RiemannianMetric
