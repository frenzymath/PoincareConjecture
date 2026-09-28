import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.M34

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {R : Type*}

theorem diagonal_tensor_contraction [CommSemiring R] (d : κ → R) (T : (ι → κ) → R) :
    (∑ a : ι → κ, ∑ b : ι → κ,
      (∏ i, Matrix.diagonal d (a i) (b i)) * T a * T b) =
    ∑ a : ι → κ, (∏ i, d (a i)) * T a ^ 2 := by
  classical
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single a]
  · simp only [Matrix.diagonal_apply_eq]
    ring
  · intro b _ hba
    have hab : ∃ i, a i ≠ b i := by
      by_contra h
      apply hba
      funext i
      exact (not_exists_not.mp h i).symm
    obtain ⟨i, hi⟩ := hab
    have hzero : (∏ j, Matrix.diagonal d (a j) (b j)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      exact Matrix.diagonal_apply_ne d hi
    rw [hzero, zero_mul, zero_mul]
  · simp

theorem diagonal_tensor_contraction_nonneg [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (d : κ → R) (hd : ∀ i, 0 ≤ d i) (T : (ι → κ) → R) :
    0 ≤ ∑ a : ι → κ, ∑ b : ι → κ,
      (∏ i, Matrix.diagonal d (a i) (b i)) * T a * T b := by
  rw [diagonal_tensor_contraction]
  exact Finset.sum_nonneg fun a _ =>
    mul_nonneg (Finset.prod_nonneg fun i _ => hd (a i)) (sq_nonneg _)

theorem diagonal_tensor_contraction_le [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (d : κ → R) (hd : ∀ i, 0 ≤ d i) (T S : (ι → κ) → R) :
    (∑ a : ι → κ, ∑ b : ι → κ,
      (∏ i, Matrix.diagonal d (a i) (b i)) * T a * T b) ≤
      2 * (∑ a : ι → κ, ∑ b : ι → κ,
        (∏ i, Matrix.diagonal d (a i) (b i)) * S a * S b) +
      2 * (∑ a : ι → κ, ∑ b : ι → κ,
        (∏ i, Matrix.diagonal d (a i) (b i)) * (T a - S a) * (T b - S b)) := by
  simp only [diagonal_tensor_contraction, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hw : 0 ≤ ∏ i, d (a i) := Finset.prod_nonneg fun i _ => hd (a i)
  have hsq : T a ^ 2 ≤ 2 * S a ^ 2 + 2 * (T a - S a) ^ 2 := by
    nlinarith [sq_nonneg (T a - 2 * S a)]
  nlinarith [mul_le_mul_of_nonneg_left hsq hw]

end PoincareConjecture.M34
