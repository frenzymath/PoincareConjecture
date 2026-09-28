import PoincareConjecture.Proofs.Horizon.LinearAlgebra.BilinearForm.Trace

open scoped BigOperators

namespace Poincare.Geometry.Curvature.Operator

variable {I : Type*} [Fintype I] [DecidableEq I]

private def elementarySkew (a b i j : I) : ℝ :=
  (if i = a then if j = b then 1 else 0 else 0) -
    (if i = b then if j = a then 1 else 0 else 0)

omit [Fintype I] in
private theorem elementarySkew_skew (a b i j : I) :
    elementarySkew a b i j = -elementarySkew a b j i := by
  simp only [elementarySkew]
  split_ifs <;> simp_all

private theorem elementarySkew_contract (a b : I) (f : I → I → ℝ) :
    (∑ i, ∑ j, elementarySkew a b i j * f i j) = f a b - f b a := by
  simp [elementarySkew, sub_mul, ite_mul, Finset.sum_sub_distrib]

private theorem elementarySkew_sq_le (a b : I) :
    (∑ i, ∑ j, (elementarySkew a b i j) ^ 2) ≤ 2 := by
  have h := elementarySkew_contract a b (elementarySkew a b)
  simp only [← pow_two] at h
  rw [h]
  simp only [elementarySkew]
  split_ifs <;> norm_num

private theorem elementarySkew_curvature_contract
    (R : I → I → I → I → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (a b c d : I) :
    (∑ i, ∑ j, ∑ k, ∑ l,
      elementarySkew a b i j * elementarySkew c d k l * R i j k l) =
      4 * R a b c d := by
  simp_rw [mul_assoc, ← Finset.mul_sum]
  simp_rw [elementarySkew_contract]
  rw [hlast a b d c, hfirst b a c d, hfirst b a d c, hlast a b d c]
  ring

theorem abs_component_le_of_operator_bound
    (R : I → I → I → I → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j)
    (hoperator : ∀ A : I → I → ℝ, (∀ i j, A i j = -A j i) →
      |∑ i, ∑ j, ∑ k, ∑ l, A i j * A k l * R i j k l| ≤
        K * ∑ i, ∑ j, (A i j) ^ 2)
    (a b c d : I) : |R a b c d| ≤ K := by
  let A := elementarySkew a b
  let B := elementarySkew c d
  have hplus := hoperator (fun i j ↦ A i j + B i j) (by
    intro i j
    dsimp [A, B]
    rw [elementarySkew_skew a b i j, elementarySkew_skew c d i j]
    ring)
  have hminus := hoperator (fun i j ↦ A i j - B i j) (by
    intro i j
    dsimp [A, B]
    rw [elementarySkew_skew a b i j, elementarySkew_skew c d i j]
    ring)
  have hpolar :
      (∑ i, ∑ j, ∑ k, ∑ l, (A i j + B i j) * (A k l + B k l) * R i j k l) -
      (∑ i, ∑ j, ∑ k, ∑ l, (A i j - B i j) * (A k l - B k l) * R i j k l) =
      16 * R a b c d := by
    simp only [add_mul, mul_add, sub_mul, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have hab := elementarySkew_curvature_contract R hfirst hlast a b c d
    have hba := elementarySkew_curvature_contract R hfirst hlast c d a b
    change (∑ i, ∑ j, ∑ k, ∑ l, A i j * B k l * R i j k l) = _ at hab
    change (∑ i, ∑ j, ∑ k, ∑ l, B i j * A k l * R i j k l) = _ at hba
    rw [hpair c d a b] at hba
    linarith
  have hnorm :
      (∑ i, ∑ j, (A i j + B i j) ^ 2) +
      (∑ i, ∑ j, (A i j - B i j) ^ 2) ≤ 8 := by
    have heq :
        (∑ i, ∑ j, (A i j + B i j) ^ 2) +
        (∑ i, ∑ j, (A i j - B i j) ^ 2) =
        2 * (∑ i, ∑ j, (A i j) ^ 2) +
        2 * (∑ i, ∑ j, (B i j) ^ 2) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq]
    linarith [elementarySkew_sq_le a b, elementarySkew_sq_le c d]
  have hp := (abs_le.mp hplus)
  have hm := (abs_le.mp hminus)
  have hnormK := mul_le_mul_of_nonneg_left hnorm hK
  apply abs_le.mpr
  constructor <;> nlinarith

end Poincare.Geometry.Curvature.Operator
