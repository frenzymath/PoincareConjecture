import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryCap
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartReparametrization











set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] space3_stereographic_dimension



theorem ballPair_cap_of_planar (hP : PlanarSchoenfliesService)
    (B : BallNeighborhoodChart E3 F)
    (c : UnitCircle → E2) (hc : IsPlanarEmbedding c) (v : UnitTwoSphere) :
    ∃ D : PlanarSchoenfliesData c, ∃ a : ℝ, a ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ B' : BallNeighborhoodChart E3 F,
        B'.inside = B.inside ∧ B'.closedRegion = B.closedRegion ∧
        B'.boundary = B.boundary ∧
        B'.chart '' {y : E3 | ‖y‖ = 1 ∧ a ≤ ⟪-(v : E3), y⟫_ℝ} =
          B.chart '' ((fun x : E2 => ((stereographic' 2 v).symm (D.chart x) : E3)) ''
            closedBall 0 1) := by
  obtain ⟨D, a, ha, G, hG, himage, _, _, _⟩ := boundaryDisc_cap_of_planar hP c hc v
  let B' := B.normReparametrize G hG
  refine ⟨D, a, ha, B', B.normReparametrize_inside G hG,
    B.normReparametrize_closedRegion G hG, B.normReparametrize_boundary G hG, ?_⟩
  rw [← himage, image_image]
  simp only [B', BallNeighborhoodChart.normReparametrize_apply, G.symm_apply_apply]

end PoincareConjecture.M25.Topology3D
