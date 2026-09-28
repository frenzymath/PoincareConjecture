import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckCurvature.InverseGram




noncomputable section
set_option autoImplicit false

open scoped BigOperators

namespace PoincareConjecture.NeckCurvature

theorem inverse_column_sum_abs_le
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1) {δ : ℝ}
    (hsmall : 2 * δ < 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ δ) (j : Fin 3) :
    (∑ i, |B i j|) ≤ cylinderInverseWeight j / (1 - 2 * δ) := by
  let S := ∑ i, |B i j|
  have hentry (i : Fin 3) : |B i j| ≤ |cylinderInverseDiagonal i j| +
      cylinderInverseWeight i * δ * S := by
    have h := abs_add_le (B i j - cylinderInverseDiagonal i j)
      (cylinderInverseDiagonal i j)
    simp only [sub_add_cancel] at h
    exact h.trans (by linarith [inverse_entry_error_le A B hAB herror i j])
  have hdiag : ∑ i, |cylinderInverseDiagonal i j| = cylinderInverseWeight j := by
    simp [cylinderInverseDiagonal, Matrix.diagonal_apply, apply_ite abs, abs_zero,
      abs_of_nonneg (cylinderInverseWeight_nonneg j)]
  have hS : S ≤ cylinderInverseWeight j + 2 * δ * S := by
    calc
      _ ≤ ∑ i, (|cylinderInverseDiagonal i j| + cylinderInverseWeight i * δ * S) :=
        Finset.sum_le_sum fun i _ => hentry i
      _ = _ := by
        rw [Finset.sum_add_distrib, hdiag, ← Finset.sum_mul, ← Finset.sum_mul,
          cylinderInverseWeight_sum]
  exact (le_div_iff₀ (by linarith : 0 < 1 - 2 * δ)).mpr (by linarith)

theorem inverse_entry_error_le_weight_product
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100) (i j : Fin 3) :
    |B i j - cylinderInverseDiagonal i j| ≤
      cylinderInverseWeight i * cylinderInverseWeight j / 98 := by
  have h := inverse_entry_error_le A B hAB herror i j
  have hcol := inverse_column_sum_abs_le A B hAB (by norm_num) herror j
  have hw := cylinderInverseWeight_nonneg i
  calc
    _ ≤ cylinderInverseWeight i * (1 / 100) * (∑ k, |B k j|) := h
    _ ≤ cylinderInverseWeight i * (1 / 100) *
        (cylinderInverseWeight j / (1 - 2 * (1 / 100))) :=
      mul_le_mul_of_nonneg_left hcol (by positivity)
    _ = _ := by ring

theorem inverse_entry_abs_le_weight_product
    (A B : Matrix (Fin 3) (Fin 3) ℝ) (hAB : A * B = 1)
    (herror : ∀ i j, |A i j - cylinderGramDiagonal i j| ≤ 1 / 100) (i j : Fin 3) :
    |B i j| ≤ |cylinderInverseDiagonal i j| +
      cylinderInverseWeight i * cylinderInverseWeight j / 98 := by
  have h := abs_add_le (B i j - cylinderInverseDiagonal i j)
    (cylinderInverseDiagonal i j)
  simp only [sub_add_cancel] at h
  exact h.trans (by linarith [inverse_entry_error_le_weight_product A B hAB herror i j])

end PoincareConjecture.NeckCurvature
