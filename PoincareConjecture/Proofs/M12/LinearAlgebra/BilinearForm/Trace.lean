import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open scoped BigOperators

namespace Poincare.LinearAlgebra

variable {I : Type*} [Fintype I]

theorem quadratic_le_trace_mul_sum_sq (B : I → I → ℝ)
    (hB : ∀ v : I → ℝ, 0 ≤ ∑ i, ∑ j, B i j * v i * v j)
    (v : I → ℝ) :
    (∑ i, ∑ j, B i j * v i * v j) ≤ (∑ i, B i i) * ∑ i, (v i) ^ 2 := by
  classical
  have hpair (i j : I) :
      0 ≤ B i i * (v j) ^ 2 - B i j * v j * v i -
        B j i * v i * v j + B j j * (v i) ^ 2 := by
    have h := hB (fun k => (if k = i then v j else 0) - (if k = j then v i else 0))
    simp only [mul_sub, sub_mul, Finset.sum_sub_distrib] at h
    simp only [mul_ite, ite_mul, mul_zero, zero_mul, Finset.sum_ite_irrel,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    nlinarith
  have hsum := Finset.sum_nonneg (s := Finset.univ) (fun i _ =>
    Finset.sum_nonneg (s := Finset.univ) (fun j _ => hpair i j))
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hsum
  have hdiag : (∑ i, ∑ j, B i i * (v j) ^ 2) =
      (∑ i, B i i) * ∑ j, (v j) ^ 2 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hdiag' : (∑ i, ∑ j, B j j * (v i) ^ 2) =
      (∑ i, B i i) * ∑ j, (v j) ^ 2 := by
    rw [Finset.sum_comm]
    exact hdiag
  have hcross : (∑ i, ∑ j, B i j * v j * v i) =
      ∑ i, ∑ j, B i j * v i * v j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcross' : (∑ i, ∑ j, B j i * v i * v j) =
      ∑ i, ∑ j, B i j * v i * v j := by
    rw [Finset.sum_comm]
    exact hcross
  rw [hdiag, hdiag', hcross, hcross'] at hsum
  linarith

end Poincare.LinearAlgebra
