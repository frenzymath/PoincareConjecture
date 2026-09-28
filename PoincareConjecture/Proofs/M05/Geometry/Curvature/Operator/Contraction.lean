
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.Reaction
import PoincareConjecture.Proofs.M05.Geometry.Curvature.Operator.ThreeDimensional










open scoped BigOperators

namespace Poincare.Geometry.Curvature.Operator


theorem cyclic_curvature_contraction_eq
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (hfirst : ∀ i j k l, R i j k l = -R j i k l)
    (hlast : ∀ i j k l, R i j k l = -R i j l k)
    (hpair : ∀ i j k l, R i j k l = R k l i j) (i j : Fin 3) :
    2 * ((∑ a, ∑ b, R (pairFirst i) a (pairSecond i) b *
        R (pairFirst j) a (pairSecond j) b) -
      (∑ a, ∑ b, R (pairFirst i) a (pairSecond i) b *
        R (pairSecond j) a (pairFirst j) b) -
      (∑ a, ∑ b, R (pairFirst i) a (pairSecond j) b *
        R (pairSecond i) a (pairFirst j) b) +
      (∑ a, ∑ b, R (pairFirst i) a (pairFirst j) b *
        R (pairSecond i) a (pairSecond j) b)) =
      curvatureReaction (curvatureMatrix R) i j := by
  have hd1 (i k l) : R i i k l = 0 := by linarith [hfirst i i k l]
  have hd2 (i j k) : R i j k k = 0 := by linarith [hlast i j k k]
  have hf10 (k l) : R 1 0 k l = -R 0 1 k l := hfirst _ _ _ _
  have hf20 (k l) : R 2 0 k l = -R 0 2 k l := hfirst _ _ _ _
  have hf21 (k l) : R 2 1 k l = -R 1 2 k l := hfirst _ _ _ _
  have hl10 (i j) : R i j 1 0 = -R i j 0 1 := hlast _ _ _ _
  have hl20 (i j) : R i j 2 0 = -R i j 0 2 := hlast _ _ _ _
  have hl21 (i j) : R i j 2 1 = -R i j 1 2 := hlast _ _ _ _
  fin_cases i <;> fin_cases j <;>
    simp [curvatureReaction, curvatureMatrix, Matrix.adjugate_apply,
      Matrix.det_fin_three, Matrix.mul_apply, Fin.sum_univ_succ,
      pairFirst, pairSecond, hd1, hd2, hf10, hf20, hf21, hl10, hl20, hl21,
      hpair 0 2 0 1, hpair 1 2 0 1, hpair 1 2 0 2] <;> ring

end Poincare.Geometry.Curvature.Operator
