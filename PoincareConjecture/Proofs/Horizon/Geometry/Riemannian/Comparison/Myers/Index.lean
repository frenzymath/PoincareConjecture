import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Index.Negative
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped RealInnerProductSpace

namespace Poincare.ODE.Jacobi

private theorem integral_polynomial_test (a b : ℝ) :
    (∫ t in (0 : ℝ)..1, a * (1 - 2 * t) ^ 2 - b * (t * (1 - t)) ^ 2) =
      a / 3 - b / 30 := by
  have hi (j : ℕ) : IntervalIntegrable (fun t : ℝ => t ^ j) volume 0 1 :=
    (continuous_id.pow j).intervalIntegrable _ _
  have hid : (∫ t in (0 : ℝ)..1, (4 * a) * t) = 2 * a := by
    rw [intervalIntegral.integral_const_mul, integral_id]
    norm_num
    ring
  calc
    _ = ∫ t in (0 : ℝ)..1,
        a - (4 * a) * t + (4 * a - b) * t ^ 2 + (2 * b) * t ^ 3 - b * t ^ 4 := by
      apply intervalIntegral.integral_congr
      intro t _
      ring
    _ = _ := by
      rw [intervalIntegral.integral_sub
        (by apply Continuous.intervalIntegrable; fun_prop) ((hi 4).const_mul b),
        intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop) ((hi 3).const_mul (2 * b)),
        intervalIntegral.integral_add
        (by apply Continuous.intervalIntegrable; fun_prop) ((hi 2).const_mul (4 * a - b)),
        intervalIntegral.integral_sub intervalIntegrable_const
          (by apply Continuous.intervalIntegrable; fun_prop)]
      rw [hid]
      simp only [intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        integral_pow]
      norm_num
      ring



theorem trace_lower_le_of_polynomial_index_nonneg {n : ℕ}
    {R : ℝ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    {k : ℝ} (hR : ContinuousOn R (Icc 0 1))
    (htrace : ∀ t ∈ Icc (0 : ℝ) 1,
      k ≤ LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (R t).toLinearMap)
    (hindex : ∀ i : Fin n, 0 ≤ indexForm R 0 1
      (indexTestField (EuclideanSpace.basisFun (Fin n) ℝ i))
      (indexTestDeriv (EuclideanSpace.basisFun (Fin n) ℝ i))
      (indexTestField (EuclideanSpace.basisFun (Fin n) ℝ i))
      (indexTestDeriv (EuclideanSpace.basisFun (Fin n) ℝ i))) :
    k ≤ 10 * (n : ℝ) := by
  classical
  let e := EuclideanSpace.basisFun (Fin n) ℝ
  let f := fun i : Fin n => indexIntegrand R
    (indexTestField (e i)) (indexTestDeriv (e i))
    (indexTestField (e i)) (indexTestDeriv (e i))
  have hint (i : Fin n) : IntervalIntegrable (f i) volume 0 1 := by
    apply intInt_indexIntegrand <;> rw [uIcc_of_le zero_le_one]
    exacts [hR, (indexTestField_cont _).continuousOn,
      (indexTestDeriv_cont _).continuousOn, (indexTestField_cont _).continuousOn,
      (indexTestDeriv_cont _).continuousOn]
  have hsum (t : ℝ) : (∑ i : Fin n, f i t) =
      (n : ℝ) * (1 - 2 * t) ^ 2 - (t * (1 - t)) ^ 2 *
        LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (R t).toLinearMap := by
    simp only [f, indexIntegrand, indexTestField, indexTestFieldTo,
      indexTestDeriv, indexTestDerivTo, real_inner_smul_left, real_inner_smul_right,
      map_smul, Finset.sum_sub_distrib]
    have he (i : Fin n) : inner ℝ (e i) (e i) = 1 := by
      rw [real_inner_self_eq_norm_sq, e.orthonormal.1 i, one_pow]
    simp only [he, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← Finset.mul_sum]
    rw [LinearMap.trace_eq_sum_inner _ e]
    simp only [ContinuousLinearMap.coe_coe, real_inner_comm (e _) (R _ _)]
    ring
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..1, ∑ i : Fin n, f i t := by
    rw [intervalIntegral.integral_finsetSum fun i _ => hint i]
    exact Finset.sum_nonneg fun i _ => hindex i
  have hupper : (∫ t in (0 : ℝ)..1, ∑ i : Fin n, f i t) ≤
      (n : ℝ) / 3 - k / 30 := by
    rw [← integral_polynomial_test (n : ℝ) k]
    apply intervalIntegral.integral_mono_on zero_le_one
      (by
        convert (IntervalIntegrable.sum Finset.univ fun i _ => hint i) using 1
        · rfl
        · ext t
          simp)
      (by apply Continuous.intervalIntegrable; fun_prop)
    intro t ht
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left (htrace t ht) (sq_nonneg (t * (1 - t)))]
  linarith

end Poincare.ODE.Jacobi
