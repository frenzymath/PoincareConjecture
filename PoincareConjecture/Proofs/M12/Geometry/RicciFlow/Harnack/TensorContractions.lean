import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*}

lemma ricciDerivative_skew (A : I → I → I → ℝ) (i j k : I) :
    A i j k - A j i k = -(A j i k - A i j k) := by
  ring

lemma ricciDerivative_cyclic (A : I → I → I → ℝ)
    (hA : ∀ i j k, A i j k = A i k j) (i j k : I) :
    (A i j k - A j i k) + (A j k i - A k j i) +
      (A k i j - A i k j) = 0 := by
  rw [hA j i k, hA k j i, hA i k j]
  ring

variable [Fintype I]

lemma ricciDerivative_trace (A : I → I → I → ℝ) (dR : I → ℝ)
    (hdiv : ∀ i, ∑ p, A p i p = dR i / 2)
    (htrace : ∀ i, ∑ p, A i p p = dR i) (i : I) :
    ∑ p, (A p i p - A i p p) = -(dR i / 2) := by
  rw [Finset.sum_sub_distrib, hdiv, htrace]
  ring

lemma ricciDerivative_trace_pairing (A : I → I → I → ℝ) (dR V : I → ℝ)
    (hdiv : ∀ i, ∑ p, A p i p = dR i / 2)
    (htrace : ∀ i, ∑ p, A i p p = dR i) :
    2 * (∑ i, (∑ p, (A p i p - A i p p)) * V i) =
      -(∑ i, dR i * V i) := by
  simp_rw [ricciDerivative_trace A dR hdiv htrace]
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma curvatureRicci_trace (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l) :
    (∑ i, ∑ k, ∑ l, Rm k i l i * Ric k l) =
      ∑ k, ∑ l, (Ric k l) ^ 2 := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_mul, hRic, pow_two]

lemma ricciSquare_trace (Ric : I → I → ℝ)
    (hsymm : ∀ i k, Ric i k = Ric k i) :
    (∑ i, ∑ k, Ric i k * Ric k i) = ∑ i, ∑ k, (Ric i k) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro k _
  rw [← hsymm i k, pow_two]

lemma harnackReaction_trace (Rm : I → I → I → I → ℝ) (Ric : I → I → ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (hsymm : ∀ i k, Ric i k = Ric k i) :
    (∑ i, (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
      ∑ k, Ric i k * Ric k i)) = ∑ i, ∑ k, (Ric i k) ^ 2 := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    curvatureRicci_trace Rm Ric hRic, ricciSquare_trace Ric hsymm]
  ring

lemma harnackTwoTensor_trace (Rm : I → I → I → I → ℝ)
    (Ric LapRic HessR : I → I → ℝ) (lapR τ : ℝ)
    (hRic : ∀ k l, ∑ i, Rm k i l i = Ric k l)
    (hsymm : ∀ i k, Ric i k = Ric k i)
    (hLap : ∑ i, LapRic i i = lapR) (hHess : ∑ i, HessR i i = lapR) :
    (∑ i, (LapRic i i - HessR i i / 2 +
      (2 * (∑ k, ∑ l, Rm k i l i * Ric k l) -
        ∑ k, Ric i k * Ric k i) + Ric i i / (2 * τ))) =
      lapR / 2 + (∑ i, ∑ k, (Ric i k) ^ 2) + (∑ i, Ric i i) / (2 * τ) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div]
  rw [hLap, hHess, ← Finset.mul_sum, curvatureRicci_trace Rm Ric hRic,
    ricciSquare_trace Ric hsymm]
  ring

end Poincare.RicciFlow.Harnack
