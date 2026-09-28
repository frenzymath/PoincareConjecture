
import Mathlib














open scoped BigOperators

namespace Poincare.Geometry.Curvature.Operator


def pairFirst : Fin 3 → Fin 3 := ![1, 2, 0]


def pairSecond : Fin 3 → Fin 3 := ![2, 0, 1]


def curvatureMatrix (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => R (pairFirst i) (pairSecond i) (pairFirst j) (pairSecond j)




noncomputable def curvatureOperator (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    EuclideanSpace ℝ (Fin 3) →ₗ[ℝ] EuclideanSpace ℝ (Fin 3) :=
  (curvatureMatrix R).toEuclideanLin


theorem curvatureMatrix_isSymm
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hpair : ∀ i j k l, R i j k l = R k l i j) :
    (curvatureMatrix R).IsSymm := by
  ext i j
  exact hpair _ _ _ _


theorem curvatureOperator_isSymmetric
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hpair : ∀ i j k l, R i j k l = R k l i j) :
    (curvatureOperator R).IsSymmetric := by
  exact Matrix.isSymmetric_toEuclideanLin_iff.mpr
    (Matrix.isHermitian_iff_isSymm.mpr (curvatureMatrix_isSymm R hpair))


theorem curvatureOperator_rayleigh
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ v (curvatureOperator R v) =
      dotProduct v ((curvatureMatrix R).mulVec v) := by
  simp [curvatureOperator, Matrix.toLpLin_apply, EuclideanSpace.inner_eq_star_dotProduct]
  exact dotProduct_comm _ _

private theorem skew_sum_sq (f : Fin 3 → Fin 3 → ℝ)
    (hskew : ∀ i j, f i j = -f j i) :
    (∑ i, ∑ j, f i j ^ 2) = 2 * ∑ a, f (pairFirst a) (pairSecond a) ^ 2 := by
  have hdiag (i) : f i i = 0 := by linarith [hskew i i]
  simp [Fin.sum_univ_succ, pairFirst, pairSecond, hdiag]
  rw [hskew 1 0, hskew 0 2, hskew 2 1]
  ring


theorem scalar_contraction_eq_twice_trace
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k) :
    (∑ i, ∑ j, R i j i j) = 2 * Matrix.trace (curvatureMatrix R) := by
  have hdiag (i) : R i i i i = 0 := by linarith [hfirst i i i i]
  have hswap (i j) : R i j i j = R j i j i := by
    rw [hfirst i j i j, hlast j i i j, neg_neg]
  simp [Matrix.trace, curvatureMatrix, Fin.sum_univ_succ, pairFirst, pairSecond, hdiag]
  rw [hswap 1 0, hswap 0 2, hswap 2 1]
  ring


theorem norm_contraction_eq_four_frobeniusSq
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k) :
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) =
      4 * ∑ i, ∑ j, curvatureMatrix R i j ^ 2 := by
  have hlastsum (i j) := skew_sum_sq (fun k l => R i j k l) (hlast i j)
  have hfirstsum (a) := skew_sum_sq
    (fun i j => R i j (pairFirst a) (pairSecond a))
    (fun i j => hfirst i j (pairFirst a) (pairSecond a))
  calc
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) =
        2 * ∑ a, ∑ i, ∑ j, R i j (pairFirst a) (pairSecond a) ^ 2 := by
      simp_rw [hlastsum]
      simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring
    _ = 4 * ∑ i, ∑ j, curvatureMatrix R i j ^ 2 := by
      simp_rw [hfirstsum]
      simp only [curvatureMatrix, Fin.sum_univ_succ, Fin.sum_univ_zero]
      ring


theorem matrix_trace_toEuclideanLin (A : Matrix (Fin 3) (Fin 3) ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) A.toEuclideanLin = A.trace := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]



theorem matrix_frobeniusSq_eq_basis_energy
    (A : Matrix (Fin 3) (Fin 3) ℝ) (hA : A.IsSymm)
    (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (∑ i, ∑ j, A i j ^ 2) = ∑ i, ‖A.toEuclideanLin (b i)‖ ^ 2 := by
  have hsym : A.toEuclideanLin.IsSymmetric :=
    Matrix.isSymmetric_toEuclideanLin_iff.mpr (Matrix.isHermitian_iff_isSymm.mpr hA)
  have henergy (c : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3))
          (A.toEuclideanLin * A.toEuclideanLin) =
        ∑ i, ‖A.toEuclideanLin (c i)‖ ^ 2 := by
    rw [LinearMap.trace_eq_sum_inner _ c]
    apply Finset.sum_congr rfl
    intro i _
    rw [Module.End.mul_apply, ← hsym]
    exact real_inner_self_eq_norm_sq _
  rw [← henergy b, henergy (EuclideanSpace.basisFun (Fin 3) ℝ)]
  simp [EuclideanSpace.norm_sq_eq, Matrix.toLpLin_apply,
    EuclideanSpace.basisFun_apply, Matrix.mulVec_single, Matrix.col]
  exact Finset.sum_comm


theorem curvatureOperator_trace
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) :
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (curvatureOperator R) =
      Matrix.trace (curvatureMatrix R) := by
  exact matrix_trace_toEuclideanLin (curvatureMatrix R)



theorem curvatureOperator_energy
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hpair : ∀ i j k l, R i j k l = R k l i j)
    (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (∑ i, ‖curvatureOperator R (b i)‖ ^ 2) =
      ∑ i, ∑ j, (curvatureMatrix R i j) ^ 2 := by
  symm
  exact matrix_frobeniusSq_eq_basis_energy (curvatureMatrix R)
    (curvatureMatrix_isSymm R hpair) b


theorem curvatureOperator_scalar_identity
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k) :
    (∑ i, ∑ j, R i j i j) =
      2 * LinearMap.trace ℝ (EuclideanSpace ℝ (Fin 3)) (curvatureOperator R) := by
  rw [scalar_contraction_eq_twice_trace R hfirst hlast, curvatureOperator_trace]



theorem curvatureOperator_normSq_identity
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j)
    (b : OrthonormalBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 3))) :
    (∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2) =
      4 * ∑ i, ‖curvatureOperator R (b i)‖ ^ 2 := by
  rw [norm_contraction_eq_four_frobeniusSq R hfirst hlast,
    curvatureOperator_energy R hpair b]

end Poincare.Geometry.Curvature.Operator
