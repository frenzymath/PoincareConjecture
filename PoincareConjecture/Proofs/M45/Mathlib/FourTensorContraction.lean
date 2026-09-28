import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic









set_option autoImplicit false

open scoped BigOperators



theorem Fintype.sum_fun_fin_four {I V : Type*} [Fintype I] [AddCommMonoid V]
    (f : (Fin 4 → I) → V) :
    ∑ a, f a = ∑ i, ∑ j, ∑ k, ∑ l, f ![i, j, k, l] := by
  classical
  let e : (I × I × I × I) ≃ (Fin 4 → I) :=
    { toFun := fun a => ![a.1, a.2.1, a.2.2.1, a.2.2.2]
      invFun := fun a => (a 0, a 1, a 2, a 3)
      left_inv := fun _ => rfl
      right_inv := fun a => by funext i; fin_cases i <;> rfl }
  rw [← e.sum_comp f]
  simp only [Fintype.sum_prod_type]
  rfl

namespace PoincareConjecture.M45



theorem sum_sq_contraction_le {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
    (A : I → K → ℝ) (B : J → K → ℝ) :
    (∑ i, ∑ j, (∑ k, A i k * B j k) ^ 2) ≤
      (∑ i, ∑ k, A i k ^ 2) * (∑ j, ∑ k, B j k ^ 2) := by
  calc
    _ ≤ ∑ i, ∑ j, (∑ k, A i k ^ 2) * (∑ k, B j k ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (A i) (B j)
    _ = _ := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]



theorem abs_sum_mul_le_cube {I : Type*} [Fintype I]
    (R B : I → ℝ) {N : ℝ} (hN : 0 ≤ N)
    (hR : ∑ i, R i ^ 2 = N ^ 2) (hB : ∑ i, B i ^ 2 ≤ N ^ 4) :
    |∑ i, R i * B i| ≤ N ^ 3 := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ R B
  rw [hR] at hCS
  have hbound := hCS.trans (mul_le_mul_of_nonneg_left hB (sq_nonneg N))
  have hsq : |∑ i, R i * B i| ^ 2 ≤ (N ^ 3) ^ 2 := by
    rw [sq_abs]
    nlinarith only [hbound]
  nlinarith only [hsq, abs_nonneg (∑ i, R i * B i), pow_nonneg hN 3]



theorem four_contraction_energy_le {I : Type*} [Fintype I]
    (R B₁ B₂ B₃ B₄ : I → ℝ) {N : ℝ} (hN : 0 ≤ N)
    (hR : ∑ i, R i ^ 2 = N ^ 2)
    (h₁ : ∑ i, B₁ i ^ 2 ≤ N ^ 4) (h₂ : ∑ i, B₂ i ^ 2 ≤ N ^ 4)
    (h₃ : ∑ i, B₃ i ^ 2 ≤ N ^ 4) (h₄ : ∑ i, B₄ i ^ 2 ≤ N ^ 4) :
    4 * (∑ i, R i * (B₁ i - B₂ i - B₃ i + B₄ i)) ≤ 16 * N ^ 3 := by
  have h1 := abs_le.mp (abs_sum_mul_le_cube R B₁ hN hR h₁)
  have h2 := abs_le.mp (abs_sum_mul_le_cube R B₂ hN hR h₂)
  have h3 := abs_le.mp (abs_sum_mul_le_cube R B₃ hN hR h₃)
  have h4 := abs_le.mp (abs_sum_mul_le_cube R B₄ hN hR h₄)
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  linarith




theorem curvature_contraction_sq_le {I : Type*} [Fintype I]
    (R : I → I → I → I → ℝ) :
    (∑ i, ∑ j, ∑ k, ∑ l, (∑ p, ∑ q, R i p j q * R k p l q) ^ 2) ≤
      (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) ^ 2 := by
  have h := sum_sq_contraction_le
    (fun (i p : I × I) => R i.1 p.1 i.2 p.2)
    (fun (i p : I × I) => R i.1 p.1 i.2 p.2)
  simp only [Fintype.sum_prod_type] at h
  have heq : (∑ i, ∑ j, ∑ p, ∑ q, R i p j q ^ 2) =
      ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  rw [heq] at h
  simpa only [pow_two] using h

end PoincareConjecture.M45
