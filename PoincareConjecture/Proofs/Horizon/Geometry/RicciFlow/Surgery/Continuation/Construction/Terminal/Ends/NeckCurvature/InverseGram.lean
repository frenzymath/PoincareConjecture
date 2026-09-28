import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.NeckCurvature

def cylinderGramDiagonal : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![2, 2, 1]

def cylinderInverseWeight : Fin 3 → ℝ := ![1 / 2, 1 / 2, 1]

def cylinderInverseDiagonal : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.diagonal cylinderInverseWeight

theorem cylinderInverseWeight_nonneg (i : Fin 3) : 0 ≤ cylinderInverseWeight i := by
  fin_cases i <;> norm_num [cylinderInverseWeight]

theorem cylinderInverseWeight_sum : ∑ i, cylinderInverseWeight i = 2 := by
  norm_num [Fin.sum_univ_succ, cylinderInverseWeight]

private theorem inverse_resolvent
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) (i j : Fin 3) :
    B i j = cylinderInverseDiagonal i j -
      cylinderInverseWeight i * ∑ k, (A i k - cylinderGramDiagonal i k) * B k j := by
  have hD : cylinderInverseDiagonal * cylinderGramDiagonal = 1 := by
    rw [cylinderInverseDiagonal, cylinderGramDiagonal, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext a
    fin_cases a <;> norm_num [cylinderInverseWeight]
  have hE : cylinderInverseDiagonal * (A - cylinderGramDiagonal) * B =
      cylinderInverseDiagonal - B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hAB, hD,
      Matrix.mul_one, Matrix.one_mul]
  have h := congrFun (congrFun hE i) j
  have hleft : (cylinderInverseDiagonal * (A - cylinderGramDiagonal) * B) i j =
      cylinderInverseWeight i * ∑ k, (A i k - cylinderGramDiagonal i k) * B k j := by
    rw [Matrix.mul_apply]
    simp only [cylinderInverseDiagonal, Matrix.diagonal_mul, Matrix.sub_apply,
      Finset.mul_sum, mul_assoc]
  rw [hleft, Matrix.sub_apply] at h
  linarith

theorem inverse_entry_error_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) {δ : ℝ}
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ δ) (i j : Fin 3) :
    |B i j - cylinderInverseDiagonal i j| ≤
      cylinderInverseWeight i * δ * ∑ k, |B k j| := by
  rw [inverse_resolvent A B hAB i j]
  have hsum : |∑ k, (A i k - cylinderGramDiagonal i k) * B k j| ≤
      δ * ∑ k, |B k j| := by
    calc
      _ ≤ ∑ k, |(A i k - cylinderGramDiagonal i k) * B k j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k, δ * |B k j| := by
        apply Finset.sum_le_sum
        intro k _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (herror i k) (abs_nonneg _)
      _ = _ := (Finset.mul_sum _ _ _).symm
  simpa only [sub_sub_cancel_left, abs_neg, abs_mul,
    abs_of_nonneg (cylinderInverseWeight_nonneg i), mul_assoc] using
    mul_le_mul_of_nonneg_left hsum (cylinderInverseWeight_nonneg i)

theorem inverse_sum_abs_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) {δ : ℝ}
    (_hδ : 0 ≤ δ) (hsmall : 2 * δ < 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ δ) :
    (∑ i, ∑ j, |B i j|) ≤ 2 / (1 - 2 * δ) := by
  let S := ∑ i, ∑ j, |B i j|
  have hentry (i j : Fin 3) : |B i j| ≤ |cylinderInverseDiagonal i j| +
      cylinderInverseWeight i * δ * ∑ k, |B k j| := by
    have h := abs_add_le (B i j - cylinderInverseDiagonal i j)
      (cylinderInverseDiagonal i j)
    simp only [sub_add_cancel] at h
    exact h.trans (by linarith [inverse_entry_error_le A B hAB herror i j])
  have hdiag (i : Fin 3) : ∑ j, |cylinderInverseDiagonal i j| = cylinderInverseWeight i := by
    simp [cylinderInverseDiagonal, Matrix.diagonal_apply, apply_ite abs, abs_zero,
      abs_of_nonneg (cylinderInverseWeight_nonneg i)]
  have hrow (i : Fin 3) : (∑ j, |B i j|) ≤
      cylinderInverseWeight i + cylinderInverseWeight i * δ * S := by
    calc
      _ ≤ ∑ j, (|cylinderInverseDiagonal i j| +
          cylinderInverseWeight i * δ * ∑ k, |B k j|) :=
        Finset.sum_le_sum fun j _ => hentry i j
      _ = _ := by rw [Finset.sum_add_distrib, hdiag, ← Finset.mul_sum, Finset.sum_comm]
  have hS : S ≤ 2 + 2 * δ * S := by
    calc
      _ ≤ ∑ i, (cylinderInverseWeight i + cylinderInverseWeight i * δ * S) :=
        Finset.sum_le_sum fun i _ => hrow i
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul,
          cylinderInverseWeight_sum]
  exact (le_div_iff₀ (by linarith : 0 < 1 - 2 * δ)).mpr (by linarith)

theorem inverse_sum_abs_le_forty_one_twentieths
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100) :
    (∑ i, ∑ j, |B i j|) ≤ 41 / 20 := by
  exact (inverse_sum_abs_le A B hAB (by norm_num) (by norm_num) herror).trans
    (by norm_num)

theorem inverse_horizontal_entry_error_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100)
    (i j : Fin 3) (hi : i ≠ 2) :
    |B i j - cylinderInverseDiagonal i j| ≤ 11 / 1000 := by
  have hw : cylinderInverseWeight i = 1 / 2 := by
    fin_cases i
    · norm_num [cylinderInverseWeight]
    · norm_num [cylinderInverseWeight]
    · exact (hi rfl).elim
  have hcol : (∑ k, |B k j|) ≤ ∑ k, ∑ l, |B k l| := by
    apply Finset.sum_le_sum
    intro k _
    exact Finset.single_le_sum (fun l _ => abs_nonneg (B k l)) (Finset.mem_univ j)
  have h := inverse_entry_error_le A B hAB herror i j
  rw [hw] at h
  have hS := inverse_sum_abs_le_forty_one_twentieths A B hAB herror
  linarith

end PoincareConjecture.NeckCurvature
