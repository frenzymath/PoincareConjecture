import PoincareConjecture.Proofs.M38.SingleCutRegions
import PoincareConjecture.Proofs.M38.TwoBallNeighborhood









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)
  (S : Set (Fin (F.event T hT).cap_count))
  (i : Fin (F.event T hT).cap_count)


theorem singleCutBall_images_disjoint :
    Disjoint ((singleCutBall F T hT P S i false).map '' Metric.ball 0 2)
      ((singleCutBall F T hT P S i true).map '' Metric.ball 0 2) := by
  have hsub (positive : Bool) :
      (singleCutBall F T hT P S i positive).map '' Metric.ball 0 2 ⊆
        Set.range (partialCappingInclude F T hT P (insert i S)
          (.inr (⟨i, Set.mem_insert i S⟩, positive))) := by
    rintro y ⟨x, hx, rfl⟩
    let z : capDoubleBall := ⟨x, hx⟩
    exact ⟨z, (partialCapBall_map F T hT P (insert i S)
      (⟨i, Set.mem_insert i S⟩, positive) z).symm⟩
  exact (partialCapPatch_disjoint F T hT P (insert i S)
    (⟨i, Set.mem_insert i S⟩, false) (⟨i, Set.mem_insert i S⟩, true)
    (by simp)).mono (hsub false) (hsub true)





theorem singleCut_exists_enclosing_ball
    (hsame : ConnectedComponents.mk ((singleCutBall F T hT P S i false).map 0) =
      ConnectedComponents.mk ((singleCutBall F T hT P S i true).map 0)) :
    ∃ C : SurgeryBallEmbedding (partialCappedCarrier F T hT P (insert i S)),
      (singleCutBall F T hT P S i false).map '' Metric.closedBall 0 (5 / 4) ∪
        (singleCutBall F T hT P S i true).map '' Metric.closedBall 0 (5 / 4) ⊆
          C.map '' Metric.ball 0 1 :=
  exists_two_ball_neighborhood
    (singleCutBall F T hT P S i false) (singleCutBall F T hT P S i true)
    (singleCutBall_images_disjoint F T hT P S i)
    (ConnectedComponents.coe_eq_coe'.mp hsame.symm)

end PoincareConjecture.M38
