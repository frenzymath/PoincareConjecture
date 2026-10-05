import PoincareLib.Geometry.Riemannian.Tensor.Regularity

/-! Source: Mapher06/Poincare-MorganTian, `PoincareMT/Statements/Ch01/CurvatureCalculus.lean`,
revision `b2c3c64781fee22edfd683a224d4f8d280e2e9ce`. Only imports and module placement are changed.
See `references/ricci-flow/mapher/shared-foundations.json`. -/


/-!
# Curvature tensor calculus interface

Morgan-Tian Chapter 1, printed pp. 3-8. This proposition states the tensor,
smoothness, symmetry, and regular-extension properties of the actual operators.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.LeviCivitaData

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Concrete tensor-calculus conclusions for the retained compatible connection. -/
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

end PoincareMT.LeviCivitaData
