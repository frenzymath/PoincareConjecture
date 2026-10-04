import PoincareLib.Geometry.RicciFlow.Curvature.Reaction
import PoincareLib.Geometry.RicciFlow.Basic
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionCoefficients
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionEndpoints
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.RicciEvolutionInterior
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Tensor.RiemannEvolutionEndpoints

/-! Adapted from Mapher06/Poincare-MorganTian, `PoincareMT/Proofs/M04/TensorEvolution.lean`,
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. See the curvature import record under
`references/ricci-flow/mapher/curvature/`. -/

/-!
# Evolution of covariant curvature tensors

The inputs remain fixed in the tangent fiber while time varies. The reactions
therefore include the Ricci input corrections. These are RicciFlowAnalysis proof obligations;
the reviewed convention and source correction are in
`reviews/declarations/tensor-evolution-v1.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

/-- The four-covariant evolution equation with within-domain time derivatives. -/
theorem hasDerivWithinAt_curvatureTensor (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (x : M) (u v w z : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).curvatureTensor x u v w z)
      ((F.connection t).tensorLaplacian (F.connection t).riemannEvaluation x ![u, v, w, z] +
        (F.connection t).curvatureReaction x u v w z) J t := by
  exact RicciFlowAnalysis.curvatureTensor_timeDerivative_extend F x u v w z
    (fun s ↦
      (F.connection s).tensorLaplacian (F.connection s).riemannEvaluation x ![u, v, w, z] +
        (F.connection s).curvatureReaction x u v w z)
    (RicciFlowAnalysis.continuousOn_curvatureTensor_evolution F x u v w z)
    (fun s hs ↦ RicciFlowAnalysis.hasDerivAt_curvatureTensor_evolution F hs x u v w z) t ht

/-- The covariant Ricci equation with the corrected curvature contraction. -/
theorem hasDerivWithinAt_ricci (F : RicciFlow n M J)
    (t : ℝ) (ht : t ∈ J) (x : M) (u v : TangentSpace (𝓡 n) x) :
    HasDerivWithinAt (fun s ↦ (F.connection s).ricci x u v)
      ((F.connection t).tensorLaplacian (F.connection t).ricciEvaluation x ![u, v] +
        (F.connection t).ricciReaction x u v) J t := by
  exact RicciFlowAnalysis.ricci_timeDerivative_extend F x u v
    (fun s ↦ (F.connection s).tensorLaplacian (F.connection s).ricciEvaluation x ![u, v] +
      (F.connection s).ricciReaction x u v)
    (RicciFlowAnalysis.continuousOn_ricciEvolutionRHS_timeSlice F x u v)
    (fun s hs ↦ RicciFlowAnalysis.hasDerivAt_ricci_evolution F hs x u v) t ht

end PoincareMT.RicciFlow

