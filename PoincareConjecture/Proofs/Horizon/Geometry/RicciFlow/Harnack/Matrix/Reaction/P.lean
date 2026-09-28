import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Tensors


set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



noncomputable def hamiltonPReaction (D : LeviCivitaData g) : CovariantTensorEvaluation n M 3 :=
  fun x z =>
    let e := g.orthonormalBasis x
    2 * (∑ i, ∑ j, D.curvatureTensor x (z 0) (e i) (z 1) (e j) *
      hamiltonP D x (e i) (e j) (z 2)) +
    2 * (∑ i, ∑ j, D.curvatureTensor x (z 0) (e i) (z 2) (e j) *
      hamiltonP D x (e i) (z 1) (e j)) +
    2 * (∑ i, ∑ j, D.curvatureTensor x (z 1) (e i) (z 2) (e j) *
      hamiltonP D x (z 0) (e i) (e j)) -
    2 * (∑ i, ∑ j, D.ricci x (e i) (e j) *
      D.covariantTensorDerivative D.riemannEvaluation x ![e i, z 0, z 1, z 2, e j])

end Poincare.RicciFlow.Harnack
