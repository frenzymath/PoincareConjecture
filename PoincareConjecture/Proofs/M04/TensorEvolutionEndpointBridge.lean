import PoincareConjecture.Proofs.M04.TensorEvolutionRHS
import PoincareConjecture.Proofs.M04.RiemannEvolutionEndpoints

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}







theorem hasDerivWithinAt_curvatureTensor_frozen_rhs
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) J t := by
  exact curvatureTensor_timeDerivative_extend F x u v w z
    (fun s ↦
      (F.connection s).tensorLaplacian (F.connection s).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection s).curvatureReaction x u v w z)
    (continuousOn_curvatureTensor_evolution F x u v w z)
    (fun s hs ↦ hasDerivAt_curvatureTensor_frozen_rhs F hs x u v w z)
    t ht

end PoincareConjecture.M04
