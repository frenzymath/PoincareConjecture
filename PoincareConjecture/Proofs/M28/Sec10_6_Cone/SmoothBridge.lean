import PoincareConjecture.Proofs.M28.Sec10_6_Cone.EndpointObstruction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

structure SmoothConeObstructionData
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ} where
  hab : a < b
  flow : RicciFlow 3 M (Icc a b)
  operator_nonnegative : ∀ t ∈ Icc a b, ∀ x,
    (flow.connection t).NonnegativeCurvatureOperator x
  point : M
  radial : TangentSpace (𝓡 3) point
  radial_ricci_null : (flow.connection b).ricci point radial radial = 0
  radius : ℝ
  radius_pos : 0 < radius
  scalar_pos : 0 < (flow.connection b).scalarCurvature point
  radial_laplacian :
    (flow.connection b).tensorLaplacian (flow.connection b).ricciEvaluation
        point ![radial, radial] =
      2 * (flow.connection b).scalarCurvature point / radius ^ 2

theorem no_smooth_cone_obstruction
    (P : RicciFlowCurvatureTheory.{u}) {a b : ℝ}
    (C : SmoothConeObstructionData (M := M) P (a := a) (b := b)) : False := by
  have hpositive : 0 < (C.flow.connection b).tensorLaplacian
      (C.flow.connection b).ricciEvaluation C.point ![C.radial, C.radial] := by
    rw [C.radial_laplacian]
    exact div_pos (mul_pos (by norm_num) C.scalar_pos)
      (sq_pos_of_pos C.radius_pos)
  exact no_positive_terminal_null_ricci_laplacian_of_operator P C.hab C.flow
    C.operator_nonnegative C.point C.radial C.radial_ricci_null hpositive

end PoincareConjecture.M28
