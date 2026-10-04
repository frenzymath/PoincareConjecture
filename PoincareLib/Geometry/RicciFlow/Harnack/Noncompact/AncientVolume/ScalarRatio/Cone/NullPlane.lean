import PoincareLib.Geometry.RicciFlow.Curvature.Calculus
import PoincareLib.Geometry.RicciFlow.Curvature.Theory
import PoincareLib.Geometry.Curvature.Operator.SectionalBounds
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Terminal null planes in ancient nonnegative curvature

A curvature component that is nonnegative for all past times and zero at
time zero has nonpositive left derivative there. The Ricci-flow curvature
equation identifies that derivative with the tensor Laplacian plus reaction.
This is the terminal-time obstruction used in Kleiner--Lott (corrected
2013), Theorem 41.2, Case 1, equation (41.9) and following paragraph,
p. 2676. The cone geometry that makes this evolution expression strictly
positive must still be constructed.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.RicciFlow

/-- The evolution of a terminal null plane cannot point out of the
nonnegative curvature cone at the right endpoint of an ancient flow. -/
theorem curvatureEvolution_nonpos_on_terminal_null_plane
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureCalculus.{u}) (F : RicciFlow n M (Iic 0))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (x : M) (v w : TangentSpace (𝓡 n) x)
    (hzero : (F.connection 0).curvatureTensor x v w v w = 0) :
    (F.connection 0).tensorLaplacian (F.connection 0).riemannEvaluation x ![v, w, v, w] +
      (F.connection 0).curvatureReaction x v w v w ≤ 0 := by
  have hmin : IsMinOn (fun t => (F.connection t).curvatureTensor x v w v w) (Iic 0) 0 := by
    intro t ht
    change (F.connection 0).curvatureTensor x v w v w ≤ _
    rw [hzero]
    exact (F.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      x (hoperator t ht x) v w
  have hcone : (-1 : ℝ) ∈ posTangentConeAt (Iic (0 : ℝ)) 0 := by
    simpa using sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Iic (0 : ℝ)).segment_subset (by simp : (0 : ℝ) ∈ Iic (0 : ℝ))
        (by norm_num : (-1 : ℝ) ∈ Iic (0 : ℝ)))
  have h := hmin.localize.hasFDerivWithinAt_nonneg
    (hC.curvature_evolution n M (Iic 0) F 0 self_mem_Iic x v w v w).hasFDerivWithinAt hcone
  change 0 ≤ (-1 : ℝ) * (_ + _) at h
  linarith

end PoincareMT.RicciFlow
