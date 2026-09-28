import PoincareConjecture.Definitions.Ch01.TensorRegularity








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


def CurvatureTensorCalculus {g : RiemannianMetric n M} (D : LeviCivitaData g) : Prop :=
  IsSmoothCovariantTensor D.riemannEvaluation ∧
  IsSmoothCovariantTensor D.ricciEvaluation ∧
  (∀ (k : ℕ) (T : CovariantTensorEvaluation n M k), IsSmoothCovariantTensor T →
    IsSmoothCovariantTensor (D.covariantTensorDerivative T)) ∧
  (∀ (x : M) (u v w z : TangentSpace (𝓡 n) x),
    D.curvatureTensor x u v w z = -D.curvatureTensor x u v z w ∧
    D.curvatureTensor x u v w z = D.curvatureTensor x w z u v ∧
    D.curvatureTensor x u v w z + D.curvatureTensor x v w u z +
      D.curvatureTensor x w u v z = 0 ∧
    D.ricci x u v = D.ricci x v u) ∧
  (∀ U : Set M, IsOpen U →
    ∀ X Y Z : (x : M) → TangentSpace (𝓡 n) x,
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞ (T% X) U →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞ (T% Y) U →
      ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓘(ℝ, EuclideanSpace ℝ (Fin n)))) ∞ (T% Z) U →
      ∀ x ∈ U, D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x))

end PoincareConjecture.LeviCivitaData
