import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Reaction.P
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction.CurvatureThree
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Tensor.Contraction.TwoFive








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

lemma isSmoothCovariantTensor_hamiltonPReaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus) :
    IsSmoothCovariantTensor (hamiltonPReaction D) := by
  unfold hamiltonPReaction
  have hP := hamiltonP_isSmoothCovariantTensor D hD
  have hA := D.isSmoothCovariantTensor_curvature_three hD hP
  have hB := D.isSmoothCovariantTensor_curvature_three_middle hD hP
  have hC := D.isSmoothCovariantTensor_curvature_three_last hD hP
  have hQ := D.isSmoothCovariantTensor_two_five_contraction hD.2.1 (hD.2.2.1 _ _ hD.1)
  simpa only [LeviCivitaData.ricciEvaluation,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] using
    (((hA.const_mul 2).add (hB.const_mul 2)).add (hC.const_mul 2)).sub (hQ.const_mul 2)

lemma covariantTensorDerivative_hamiltonPReaction
    (D : LeviCivitaData g) (hD : D.CurvatureTensorCalculus)
    (x : M) (p a b c : TangentSpace (𝓡 n) x) :
    let e := g.orthonormalBasis x
    let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
    D.covariantTensorDerivative (hamiltonPReaction D) x ![p, a, b, c] =
      2 * (∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, a, e i, b, e j] *
        hamiltonP D x (e i) (e j) c + D.curvatureTensor x a (e i) b (e j) *
        D.covariantTensorDerivative P x ![p, e i, e j, c])) +
      2 * (∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, a, e i, c, e j] *
        hamiltonP D x (e i) b (e j) + D.curvatureTensor x a (e i) c (e j) *
        D.covariantTensorDerivative P x ![p, e i, b, e j])) +
      2 * (∑ i, ∑ j, (D.covariantTensorDerivative D.riemannEvaluation x ![p, b, e i, c, e j] *
        hamiltonP D x a (e i) (e j) + D.curvatureTensor x b (e i) c (e j) *
        D.covariantTensorDerivative P x ![p, a, e i, e j])) -
      2 * (∑ i, ∑ j, (D.covariantTensorDerivative D.ricciEvaluation x ![p, e i, e j] *
        D.covariantTensorDerivative D.riemannEvaluation x ![e i, a, b, c, e j] +
        D.ricci x (e i) (e j) * D.covariantTensorDerivative
          (D.covariantTensorDerivative D.riemannEvaluation) x ![p, e i, a, b, c, e j])) := by
  let P : CovariantTensorEvaluation n M 3 := fun y z => hamiltonP D y (z 0) (z 1) (z 2)
  let A : CovariantTensorEvaluation n M 3 := fun y z =>
    ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 1)
      (g.orthonormalBasis y j) * P y ![g.orthonormalBasis y i, g.orthonormalBasis y j, z 2]
  let B : CovariantTensorEvaluation n M 3 := fun y z =>
    ∑ i, ∑ j, D.curvatureTensor y (z 0) (g.orthonormalBasis y i) (z 2)
      (g.orthonormalBasis y j) * P y ![g.orthonormalBasis y i, z 1, g.orthonormalBasis y j]
  let C : CovariantTensorEvaluation n M 3 := fun y z =>
    ∑ i, ∑ j, D.curvatureTensor y (z 1) (g.orthonormalBasis y i) (z 2)
      (g.orthonormalBasis y j) * P y ![z 0, g.orthonormalBasis y i, g.orthonormalBasis y j]
  let Q : CovariantTensorEvaluation n M 3 := fun y z =>
    ∑ i, ∑ j, D.ricciEvaluation y ![g.orthonormalBasis y i, g.orthonormalBasis y j] *
      D.covariantTensorDerivative D.riemannEvaluation y
        ![g.orthonormalBasis y i, z 0, z 1, z 2, g.orthonormalBasis y j]
  have hP := hamiltonP_isSmoothCovariantTensor D hD
  have hA : IsSmoothCovariantTensor A := D.isSmoothCovariantTensor_curvature_three hD hP
  have hB : IsSmoothCovariantTensor B := D.isSmoothCovariantTensor_curvature_three_middle hD hP
  have hC : IsSmoothCovariantTensor C := D.isSmoothCovariantTensor_curvature_three_last hD hP
  have hQ : IsSmoothCovariantTensor Q :=
    D.isSmoothCovariantTensor_two_five_contraction hD.2.1 (hD.2.2.1 _ _ hD.1)
  have heq : hamiltonPReaction D = fun y z => 2 * A y z + 2 * B y z + 2 * C y z - 2 * Q y z := rfl
  rw [heq, D.covariantTensorDerivative_sub
    (((hA.const_mul 2).add (hB.const_mul 2)).add (hC.const_mul 2)) (hQ.const_mul 2),
    D.covariantTensorDerivative_add ((hA.const_mul 2).add (hB.const_mul 2)) (hC.const_mul 2),
    D.covariantTensorDerivative_add (hA.const_mul 2) (hB.const_mul 2),
    D.covariantTensorDerivative_const_mul hA, D.covariantTensorDerivative_const_mul hB,
    D.covariantTensorDerivative_const_mul hC, D.covariantTensorDerivative_const_mul hQ]
  dsimp only [A, B, C, Q]
  rw [D.covariantTensorDerivative_curvature_three hD hP,
    D.covariantTensorDerivative_curvature_three_middle hD hP,
    D.covariantTensorDerivative_curvature_three_last hD hP,
    D.covariantTensorDerivative_two_five_contraction hD.2.1 (hD.2.2.1 _ _ hD.1)]
  rfl

end Poincare.RicciFlow.Harnack
