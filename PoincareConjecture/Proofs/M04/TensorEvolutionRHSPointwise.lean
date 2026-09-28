import PoincareConjecture.Proofs.M04.TensorEvolutionRHS










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}






theorem curvatureTensor_second_derivative_commutator_eq_sub_insertion
    (D : LeviCivitaData g) (x : M)
    (a b c d e f : TangentSpace (𝓡 n) x) :
    D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![a, b, c, d, e, f] =
      D.iteratedCovariantTensorDerivative D.riemannEvaluation 2 x
        ![b, a, c, d, e, f] -
        (∑ i, D.riemannEvaluation x
          (Function.update ![c, d, e, f] i
            (D.curvature x a b (![c, d, e, f] i)))) := by
  have h := curvatureTensor_second_derivative_commutator D x a b c d e f
  linarith







theorem curvature_frozen_rhs_eq_firstVariation
    (D : LeviCivitaData g) (x : M)
    (a b c d : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![a, b, c, d] +
        D.curvatureReaction x a b c d =
      -2 * D.ricci x (D.curvature x a b d) c -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, b, d, c] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, d, b, c] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![a, c, b, d] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, a, d, c] +
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, d, a, c] -
        D.iteratedCovariantTensorDerivative D.ricciEvaluation 2 x ![b, c, a, d] := by
  exact (curvature_firstVariation_rhs_eq_frozen D x a b c d).symm

end PoincareConjecture.M04
