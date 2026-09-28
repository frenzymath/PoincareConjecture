import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

open scoped RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_principal_contraction_le
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    ‖∑ i : ι, ∑ j : ι,
      inner ℝ (EuclideanSpace.basisFun ι ℝ i) (a (EuclideanSpace.basisFun ι ℝ j)) •
        D (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * ‖a‖ * ‖D‖ := by
  classical
  let e := EuclideanSpace.basisFun ι ℝ
  have hentry (i j : ι) : ‖inner ℝ (e i) (a (e j))‖ ≤ ‖a‖ := by
    calc
      ‖inner ℝ (e i) (a (e j))‖ ≤ ‖e i‖ * ‖a (e j)‖ := norm_inner_le_norm _ _
      _ ≤ ‖e i‖ * (‖a‖ * ‖e j‖) :=
        mul_le_mul_of_nonneg_left (a.le_opNorm _) (norm_nonneg _)
      _ = ‖a‖ := by simp [e]
  have hD (i j : ι) : ‖D (e i) (e j)‖ ≤ ‖D‖ := by
    calc
      ‖D (e i) (e j)‖ ≤ ‖D (e i)‖ * ‖e j‖ := (D _).le_opNorm _
      _ ≤ (‖D‖ * ‖e i‖) * ‖e j‖ :=
        mul_le_mul_of_nonneg_right (D.le_opNorm _) (norm_nonneg _)
      _ = ‖D‖ := by simp [e]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, ‖inner ℝ (e i) (a (e j)) • D (e i) (e j)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : ι, ∑ _j : ι, ‖a‖ * ‖D‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      rw [norm_smul]
      exact mul_le_mul (hentry i j) (hD i j) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

theorem norm_freezing_defect_le
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F}
    {H M α : ℝ} (hH : 0 ≤ H)
    {x y : EuclideanSpace ℝ ι}
    (ha : ‖a y - a x‖ ≤ H * ‖y - x‖ ^ α) (hD : ‖D‖ ≤ M) :
    ‖∑ i : ι, ∑ j : ι,
      inner ℝ (EuclideanSpace.basisFun ι ℝ i)
        ((a y - a x) (EuclideanSpace.basisFun ι ℝ j)) •
        D (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j)‖ ≤
      ((Fintype.card ι : ℝ) ^ 2 * H * M) * ‖y - x‖ ^ α := by
  refine (norm_principal_contraction_le (a y - a x) D).trans ?_
  calc
    (Fintype.card ι : ℝ) ^ 2 * ‖a y - a x‖ * ‖D‖ ≤
        (Fintype.card ι : ℝ) ^ 2 * (H * ‖y - x‖ ^ α) * M := by gcongr
    _ = _ := by ring

end Poincare.Parabolic.Interior
