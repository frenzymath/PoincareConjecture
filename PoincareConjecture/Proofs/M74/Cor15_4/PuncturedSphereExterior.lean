import PoincareConjecture.Proofs.M54.ConnectedSum.Coordinates
import PoincareConjecture.Proofs.M74.Cor15_4.PuncturedSphereChart











set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SurgeryBallEmbedding

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)



theorem closedBall_compl_nonempty : B.closedBallᶜ.Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq StandardCapSpace (by norm_num : (0 : ℝ) ≤ 3 / 2)
  have hxball : x ∈ ball (0 : StandardCapSpace) 2 := by
    rw [mem_ball_zero_iff, hx]
    norm_num
  refine ⟨B.map x, (B.map_mem_complement_iff hxball).mpr ?_⟩
  rw [hx]
  norm_num

variable (d : Diffeomorph (𝓡 3) (𝓡 3) A.carrier ThreeSphere ∞)



theorem punctureChart_image_closedBall_compl_isOpen :
    IsOpen ((B.punctureChart d) '' B.closedBallᶜ) :=
  (B.punctureChart d).isOpen_image_of_subset_source B.closedBall_closed.isOpen_compl
    (B.closedBall_compl_subset_punctureChart_source d)



theorem punctureChart_image_closedBall_compl_isBounded :
    Bornology.IsBounded ((B.punctureChart d) '' B.closedBallᶜ) := by
  apply (B.punctureChart_image_exterior_isCompact d (r := 1)
    (by norm_num) (by norm_num)).isBounded.subset
  apply image_mono
  exact compl_subset_compl.mpr (image_mono ball_subset_closedBall)



theorem punctureChart_image_closedBall_compl_nonempty :
    ((B.punctureChart d) '' B.closedBallᶜ).Nonempty :=
  B.closedBall_compl_nonempty.image _

end PoincareConjecture.SurgeryBallEmbedding
