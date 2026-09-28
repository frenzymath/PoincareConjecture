import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.InverseGram

noncomputable section
set_option autoImplicit false
set_option maxRecDepth 4000

open scoped BigOperators

namespace PoincareConjecture.NeckCurvature

def cylinderCurvatureComponent (i j k l : Fin 3) : ℝ :=
  2 * ((if i = 0 ∧ j = 1 then 1 else 0) - (if i = 1 ∧ j = 0 then 1 else 0)) *
    ((if k = 0 ∧ l = 1 then 1 else 0) - (if k = 1 ∧ l = 0 then 1 else 0))

theorem cylinder_double_contraction (B : Matrix (Fin 3) (Fin 3) ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * cylinderCurvatureComponent i k j l) =
      4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) := by
  norm_num [Fin.sum_univ_succ, cylinderCurvatureComponent,
    show (2 : Fin 3) ≠ 1 by decide]
  ring

theorem abs_cylinder_double_contraction_sub_one_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100) :
    |4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) - 1| ≤ 45 / 1000 := by
  have h00 := inverse_horizontal_entry_error_le A B hAB herror 0 0 (by decide)
  have h11 := inverse_horizontal_entry_error_le A B hAB herror 1 1 (by decide)
  have h01 := inverse_horizontal_entry_error_le A B hAB herror 0 1 (by decide)
  have h10 := inverse_horizontal_entry_error_le A B hAB herror 1 0 (by decide)
  norm_num [cylinderInverseDiagonal, Matrix.diagonal_apply, cylinderInverseWeight,
    Fin.ext_iff] at h00 h11 h01 h10
  have hx0 : 0 ≤ B 0 0 := by linarith [(abs_le.mp h00).1]
  have hy0 : 0 ≤ B 1 1 := by linarith [(abs_le.mp h11).1]
  have hp0 : (489 / 1000 : ℝ) ^ 2 ≤ B 0 0 * B 1 1 := by
    have hx : (489 / 1000 : ℝ) ≤ B 0 0 := by linarith [(abs_le.mp h00).1]
    have hy : (489 / 1000 : ℝ) ≤ B 1 1 := by linarith [(abs_le.mp h11).1]
    simpa only [pow_two] using mul_le_mul hx hy (by norm_num) hx0
  have hp1 : B 0 0 * B 1 1 ≤ (511 / 1000 : ℝ) ^ 2 := by
    have hx : B 0 0 ≤ (511 / 1000 : ℝ) := by linarith [(abs_le.mp h00).2]
    have hy : B 1 1 ≤ (511 / 1000 : ℝ) := by linarith [(abs_le.mp h11).2]
    simpa only [pow_two] using mul_le_mul hx hy hy0 (by norm_num)
  have hcross : |B 0 1 * B 1 0| ≤ (11 / 1000 : ℝ) ^ 2 := by
    rw [abs_mul]
    simpa only [pow_two] using mul_le_mul h01 h10 (abs_nonneg _) (by norm_num)
  apply abs_le.mpr
  constructor <;> nlinarith only [hp0, hp1, (abs_le.mp hcross).1, (abs_le.mp hcross).2]

theorem abs_double_contraction_error_le
    (B : Matrix (Fin 3) (Fin 3) ℝ) (R R₀ : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    {δ : ℝ} (hR : ∀ i j k l, |R i j k l - R₀ i j k l| ≤ δ) :
    |(∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R i k j l) -
      (∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R₀ i k j l)| ≤
        (∑ i, ∑ j, |B i j|) ^ 2 * δ := by
  simp only [← Finset.sum_sub_distrib, ← mul_sub]
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, |B i j * B k l * (R i k j l - R₀ i k j l)| := by
      calc
        _ ≤ ∑ i, |∑ j, ∑ k, ∑ l, B i j * B k l * (R i k j l - R₀ i k j l)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := Finset.sum_le_sum fun i _ =>
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ =>
              Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ i, ∑ j, ∑ k, ∑ l, |B i j| * |B k l| * δ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro k _
      apply Finset.sum_le_sum
      intro l _
      simp only [abs_mul]
      exact mul_le_mul_of_nonneg_left (hR i k j l) (by positivity)
    _ = _ := by simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc, mul_left_comm]

theorem abs_scalar_sub_one_lt_half
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ i j k l, |R i j k l - cylinderCurvatureComponent i j k l| ≤ 103 / 1000) :
    |(∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R i k j l) - 1| < 1 / 2 := by
  have he := abs_double_contraction_error_le B R cylinderCurvatureComponent hR
  rw [cylinder_double_contraction] at he
  have hm := abs_cylinder_double_contraction_sub_one_le A B hAB herror
  have hS := inverse_sum_abs_le_forty_one_twentieths A B hAB herror
  have hS0 : 0 ≤ ∑ i, ∑ j, |B i j| := by positivity
  have hS2 := mul_self_le_mul_self hS0 hS
  have htri := abs_add_le
    ((∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R i k j l) -
      4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0))
    (4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) - 1)
  rw [sub_add_sub_cancel] at htri
  nlinarith only [he, hm, hS2, htri]

theorem abs_scalar_sub_one_lt_third
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hR : ∀ i j k l, |R i j k l - cylinderCurvatureComponent i j k l| ≤ 63 / 1000) :
    |(∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R i k j l) - 1| < 1 / 3 := by
  have he := abs_double_contraction_error_le B R cylinderCurvatureComponent hR
  rw [cylinder_double_contraction] at he
  have hm := abs_cylinder_double_contraction_sub_one_le A B hAB herror
  have hS := inverse_sum_abs_le_forty_one_twentieths A B hAB herror
  have hS0 : 0 ≤ ∑ i, ∑ j, |B i j| := by positivity
  have hS2 := mul_self_le_mul_self hS0 hS
  have htri := abs_add_le
    ((∑ i, ∑ j, ∑ k, ∑ l, B i j * B k l * R i k j l) -
      4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0))
    (4 * (B 0 0 * B 1 1 - B 0 1 * B 1 0) - 1)
  rw [sub_add_sub_cancel] at htri
  nlinarith only [he, hm, hS2, htri]

end PoincareConjecture.NeckCurvature
