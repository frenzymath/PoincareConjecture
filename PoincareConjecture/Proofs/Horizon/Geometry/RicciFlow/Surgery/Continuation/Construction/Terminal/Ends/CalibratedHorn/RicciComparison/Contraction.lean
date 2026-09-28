import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.RicciComparison.InverseGram
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.ScalarBounds




noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000

open scoped BigOperators

attribute [local simp] Matrix.cons_val_two

namespace PoincareConjecture.NeckCurvature

private theorem fin_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide
private theorem fin_two_ne_one : (2 : Fin 3) ≠ 1 := by decide
private theorem fin_zero_ne_two : (0 : Fin 3) ≠ 2 := by decide
private theorem fin_one_ne_two : (1 : Fin 3) ≠ 2 := by decide
attribute [local simp] fin_two_ne_zero fin_two_ne_one fin_zero_ne_two fin_one_ne_two

def cylinderRicciDiagonal : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![1, 1, 0]

def cylinderRicciError : Matrix (Fin 3) (Fin 3) ℝ :=
  !![21 / 200, 7 / 100, 17 / 500;
     7 / 100, 21 / 200, 17 / 500;
     17 / 500, 17 / 500, 13 / 200]

theorem cylinder_ricci_contraction (a b : Fin 3) :
    (∑ i, ∑ j, cylinderInverseDiagonal i j * cylinderCurvatureComponent a i b j) =
      cylinderRicciDiagonal a b := by
  fin_cases a <;> fin_cases b <;>
    norm_num [Fin.sum_univ_three, cylinderInverseDiagonal, cylinderInverseWeight,
      cylinderCurvatureComponent, cylinderRicciDiagonal, Matrix.diagonal_apply]

theorem abs_ricci_contraction_sub_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (hmetric : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ a b j, R a a b j = 0) (hlast : ∀ a i b, R a i b b = 0)
    (hR : ∀ a i b j, |R a i b j - cylinderCurvatureComponent a i b j| ≤ 63 / 1000)
    (a b : Fin 3) :
    |(∑ i, ∑ j, B i j * R a i b j) - cylinderRicciDiagonal a b| ≤
      cylinderRicciError a b := by
  let E (i j : Fin 3) :=
    (if i = a ∨ j = b then 0 else
      (|cylinderInverseDiagonal i j| +
        cylinderInverseWeight i * cylinderInverseWeight j / 98) * (63 / 1000)) +
    cylinderInverseWeight i * cylinderInverseWeight j / 98 *
      |cylinderCurvatureComponent a i b j|
  have hterm (i j : Fin 3) :
      |B i j * R a i b j - cylinderInverseDiagonal i j *
        cylinderCurvatureComponent a i b j| ≤ E i j := by
    have hdiff : |B i j * (R a i b j - cylinderCurvatureComponent a i b j)| ≤
        if i = a ∨ j = b then 0 else
          (|cylinderInverseDiagonal i j| +
            cylinderInverseWeight i * cylinderInverseWeight j / 98) * (63 / 1000) := by
      split_ifs with hij
      · rcases hij with rfl | rfl
        · have hz : cylinderCurvatureComponent i i b j = 0 := by
            fin_cases i <;> simp [cylinderCurvatureComponent]
          simp [hfirst, hz]
        · have hz : cylinderCurvatureComponent a i j j = 0 := by
            fin_cases j <;> simp [cylinderCurvatureComponent]
          simp [hlast, hz]
      · rw [abs_mul]
        exact mul_le_mul (inverse_entry_abs_le_weight_product A B hAB hmetric i j)
          (hR a i b j) (abs_nonneg _)
          (add_nonneg (abs_nonneg _) (div_nonneg
            (mul_nonneg (cylinderInverseWeight_nonneg i) (cylinderInverseWeight_nonneg j))
            (by norm_num)))
    have hmodel : |(B i j - cylinderInverseDiagonal i j) *
        cylinderCurvatureComponent a i b j| ≤
        cylinderInverseWeight i * cylinderInverseWeight j / 98 *
          |cylinderCurvatureComponent a i b j| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right
        (inverse_entry_error_le_weight_product A B hAB hmetric i j) (abs_nonneg _)
    calc
      _ = |B i j * (R a i b j - cylinderCurvatureComponent a i b j) +
          (B i j - cylinderInverseDiagonal i j) * cylinderCurvatureComponent a i b j| :=
        congrArg abs (by ring)
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hdiff hmodel)
  have hsum : |(∑ i, ∑ j, B i j * R a i b j) - cylinderRicciDiagonal a b| ≤
      ∑ i, ∑ j, E i j := by
    rw [← cylinder_ricci_contraction a b]
    simp only [← Finset.sum_sub_distrib]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ =>
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => hterm i j))
  apply hsum.trans
  fin_cases a <;> fin_cases b <;>
    norm_num [E, Fin.sum_univ_three, cylinderInverseDiagonal, cylinderInverseWeight,
      cylinderCurvatureComponent, cylinderRicciError, Matrix.diagonal_apply] <;>
    norm_num [Fin.ext_iff]

theorem abs_ricci_quadratic_error_le
    (R : Matrix (Fin 3) (Fin 3) ℝ)
    (hR : ∀ i j, |R i j - cylinderRicciDiagonal i j| ≤ cylinderRicciError i j)
    (v : Fin 3 → ℝ) :
    |(∑ i, ∑ j, v i * v j * R i j) - (v 0 ^ 2 + v 1 ^ 2)| ≤
      (7 / 50 : ℝ) * (2 * v 0 ^ 2 + 2 * v 1 ^ 2 + v 2 ^ 2) := by
  have hmodel : (∑ i, ∑ j, v i * v j * cylinderRicciDiagonal i j) =
      v 0 ^ 2 + v 1 ^ 2 := by
    norm_num [Fin.sum_univ_three, cylinderRicciDiagonal, Matrix.diagonal_apply]
    ring
  have hsum : |(∑ i, ∑ j, v i * v j * R i j) - (v 0 ^ 2 + v 1 ^ 2)| ≤
      ∑ i, ∑ j, |v i| * |v j| * cylinderRicciError i j := by
    rw [← hmodel]
    simp only [← Finset.sum_sub_distrib, ← mul_sub]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro i _
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro j _
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_left (hR i j) (by positivity)
  apply hsum.trans
  norm_num [Fin.sum_univ_succ, cylinderRicciError]
  have h01 := sq_nonneg (|v 0| - |v 1|)
  have h02 := sq_nonneg (|v 0| - |v 2|)
  have h12 := sq_nonneg (|v 1| - |v 2|)
  nlinarith [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2), sq_nonneg (v 0),
    sq_nonneg (v 1), sq_nonneg (v 2)]

end PoincareConjecture.NeckCurvature
