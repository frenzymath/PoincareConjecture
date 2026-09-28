import PoincareConjecture.Definitions.Ch03.CurvatureReaction
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M04.RicciEvolutionCoefficients
import PoincareConjecture.Proofs.M04.RicciEvolutionEndpoints
import PoincareConjecture.Proofs.M04.RicciEvolutionInterior
import PoincareConjecture.Proofs.M04.RiemannEvolutionEndpoints










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}


theorem hasDerivWithinAt_curvatureTensor (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) J t := by
  exact M04.curvatureTensor_timeDerivative_extend F x u v w z
    (fun s ↦
      (F.connection s).tensorLaplacian (F.connection s).riemannEvaluation x ![u, v, w, z] +
        (F.connection s).curvatureReaction x u v w z)
    (M04.continuousOn_curvatureTensor_evolution F x u v w z)
    (fun s hs ↦ M04.hasDerivAt_curvatureTensor_evolution F hs x u v w z) t ht


theorem hasDerivWithinAt_ricci (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v)
      ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, v] +
        (F.connection t).ricciReaction x u v) J t := by
  exact M04.ricci_timeDerivative_extend F x u v
    (fun s ↦ (F.connection s).tensorLaplacian (F.connection s).ricciEvaluation x ![u, v] +
      (F.connection s).ricciReaction x u v)
    (M04.continuousOn_ricciEvolutionRHS_timeSlice F x u v)
    (fun s hs ↦ M04.hasDerivAt_ricci_evolution F hs x u v) t ht

end PoincareConjecture.RicciFlow

