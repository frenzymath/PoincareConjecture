import PoincareConjecture.Proofs.M04.RicciEvolutionCoefficients
import PoincareConjecture.Proofs.M04.RicciEvolutionEndpoints
import PoincareConjecture.Proofs.M04.RicciEvolutionInterior

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem hasDerivWithinAt_ricci_frozen_rhs
    (F : RicciFlow n M J) (t : ℝ) (ht : t ∈ J) (x : M)
    (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v)
      ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation
          x ![u, v] +
        (F.connection t).ricciReaction x u v) J t := by
  exact ricci_timeDerivative_extend F x u v
    (fun s ↦
      (F.connection s).tensorLaplacian (F.connection s).ricciEvaluation
          x ![u, v] +
        (F.connection s).ricciReaction x u v)
    (continuousOn_ricciEvolutionRHS_timeSlice F x u v)
    (fun s hs ↦ hasDerivAt_ricci_evolution F hs x u v) t ht

end PoincareConjecture.M04
