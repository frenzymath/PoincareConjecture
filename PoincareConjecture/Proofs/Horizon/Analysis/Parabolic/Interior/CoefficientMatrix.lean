import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Coefficients
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.FrozenPositiveDefinite








noncomputable section

open scoped RealInnerProductSpace BigOperators

namespace Poincare.Parabolic.Interior

variable {ι F : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


def coefficientMatrix
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm a

@[simp]
theorem toEuclideanCLM_coefficientMatrix
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ) (coefficientMatrix a) = a :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).apply_symm_apply a

@[simp]
theorem coefficientMatrix_apply
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) (i j : ι) :
    coefficientMatrix a i j =
      inner ℝ (EuclideanSpace.basisFun ι ℝ i) (a (EuclideanSpace.basisFun ι ℝ j)) := by
  exact LinearMap.toMatrixOrthonormal_apply_apply
    (EuclideanSpace.basisFun ι ℝ) a.toLinearMap i j

theorem coefficientMatrix_isHermitian
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (ha : ∀ v w, inner ℝ (a v) w = inner ℝ v (a w)) :
    (coefficientMatrix a).IsHermitian := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mp
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    toEuclideanCLM_coefficientMatrix]
  exact ha

theorem coefficientMatrix_posDef
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (ha : ∀ v w, inner ℝ (a v) w = inner ℝ v (a w))
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (a v)) :
    (coefficientMatrix a).PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos (coefficientMatrix_isHermitian a ha)
  intro x hx
  let v : EuclideanSpace ℝ ι := WithLp.toLp 2 x
  have hv : v ≠ 0 := by simpa [v] using hx
  have hpos : 0 < inner ℝ v (a v) :=
    (mul_pos hlam (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hell v)
  rw [← toEuclideanCLM_coefficientMatrix a, Matrix.inner_toEuclideanCLM] at hpos
  simpa [v] using hpos

theorem matrixLap_coefficientMatrix
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    Kernel.matrixLap (coefficientMatrix a) D =
      ∑ i : ι, ∑ j : ι,
        inner ℝ (EuclideanSpace.basisFun ι ℝ i)
          (a (EuclideanSpace.basisFun ι ℝ j)) •
        D (EuclideanSpace.basisFun ι ℝ i) (EuclideanSpace.basisFun ι ℝ j) := by
  simp [Kernel.matrixLap]

@[simp]
theorem coefficientMatrix_sub
    (a b : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    coefficientMatrix (a - b) = coefficientMatrix a - coefficientMatrix b :=
  (Matrix.toEuclideanCLM (n := ι) (𝕜 := ℝ)).symm.map_sub a b

theorem norm_matrixLap_coefficientMatrix_le
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F) :
    ‖Kernel.matrixLap (coefficientMatrix a) D‖ ≤
      (Fintype.card ι : ℝ) ^ 2 * ‖a‖ * ‖D‖ := by
  rw [matrixLap_coefficientMatrix]
  exact norm_principal_contraction_le a D



theorem norm_matrixLap_coefficientMatrix_sub_le
    {a : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}
    {D : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι →L[ℝ] F}
    {H M α : ℝ} (hH : 0 ≤ H) {x y : EuclideanSpace ℝ ι}
    (ha : ‖a y - a x‖ ≤ H * ‖y - x‖ ^ α) (hD : ‖D‖ ≤ M) :
    ‖Kernel.matrixLap (coefficientMatrix (a y) - coefficientMatrix (a x)) D‖ ≤
      ((Fintype.card ι : ℝ) ^ 2 * H * M) * ‖y - x‖ ^ α := by
  rw [← coefficientMatrix_sub, matrixLap_coefficientMatrix]
  exact norm_freezing_defect_le hH ha hD


theorem norm_coefficient_le
    (a : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (ha : ∀ v w, inner ℝ (a v) w = inner ℝ v (a w))
    {lam upper : ℝ} (hlam : 0 < lam) (hupper : 0 ≤ upper)
    (hell : ∀ v, lam * ‖v‖ ^ 2 ≤ inner ℝ v (a v))
    (hbound : ∀ v, inner ℝ v (a v) ≤ upper * ‖v‖ ^ 2) :
    ‖a‖ ≤ upper := by
  let A := coefficientMatrix a
  have hA : A.PosDef := coefficientMatrix_posDef a ha hlam hell
  let L := Kernel.spdSqrtEquiv A hA
  have hL (v : EuclideanSpace ℝ ι) : ‖L v‖ ≤ Real.sqrt upper * ‖v‖ := by
    apply Kernel.spdSqrt_apply_le A hA hupper
    simpa only [A, toEuclideanCLM_coefficientMatrix] using hbound
  have hLL (v : EuclideanSpace ℝ ι) : L (L v) = a v := by
    simpa only [A, toEuclideanCLM_coefficientMatrix] using Kernel.spdSqrt_comp A hA v
  apply a.opNorm_le_bound hupper
  intro v
  calc
    ‖a v‖ = ‖L (L v)‖ := congrArg norm (hLL v).symm
    _ ≤ Real.sqrt upper * ‖L v‖ := hL _
    _ ≤ Real.sqrt upper * (Real.sqrt upper * ‖v‖) :=
      mul_le_mul_of_nonneg_left (hL v) (Real.sqrt_nonneg _)
    _ = upper * ‖v‖ := by rw [← mul_assoc, Real.mul_self_sqrt hupper]

end Poincare.Parabolic.Interior
