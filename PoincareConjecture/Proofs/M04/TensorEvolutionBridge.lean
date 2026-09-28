import PoincareConjecture.Proofs.M04.CurvatureDerivativeEvolution

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.M04

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {J : Set ℝ}


theorem curvatureTensor_evolution_rhs_zero
    (D : LeviCivitaData g) (x : M)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.tensorLaplacian D.riemannEvaluation x ![u, v, w, z] +
        curvatureDerivativeReaction D 0 x ![u, v, w, z] =
      D.tensorLaplacian D.riemannEvaluation x ![u, v, w, z] +
        D.curvatureReaction x u v w z := by
  simp only [curvatureDerivativeReaction]
  rfl


theorem hasDerivAt_curvatureTensor_evolution_from_iterated
    (F : RicciFlow n M J) (x : M)
    {t : ℝ} (ht : t ∈ interior J)
    (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation
          x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) t := by
  exact hasDerivAt_iteratedRiemann_evolution F 0 ht x ![u, v, w, z]

end PoincareConjecture.M04
