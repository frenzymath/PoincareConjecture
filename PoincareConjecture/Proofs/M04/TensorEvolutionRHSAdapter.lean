import PoincareConjecture.Proofs.M04.TensorEvolutionRHS










set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem hasDerivAt_curvatureTensor_frozen_rhs_adapter
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) t := by
  refine (hasDerivAt_curvatureTensor_first_variation F ht x u v w z).congr_deriv ?_
  exact curvature_firstVariation_rhs_eq_frozen (F.connection t) x u v w z

end PoincareConjecture.M04
