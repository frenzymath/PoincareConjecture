import PoincareConjecture.Proofs.M38.SphereTwoBallReduction
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.OpenPartialHomeomorph.IsImage










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)



noncomputable def surgeryBallPartialHomeomorph :
    OpenPartialHomeomorph StandardCapSpace A.carrier where
  toFun := B.map
  invFun := B.inverse
  source := Metric.ball 0 2
  target := B.map '' Metric.ball 0 2
  map_source' := fun _ hx => Set.mem_image_of_mem _ hx
  map_target' := fun _ hx => surgeryBall_inverse_mem B hx
  left_inv' := B.left_inverse
  right_inv' := B.right_inverse
  open_source := Metric.isOpen_ball
  open_target := surgeryBall_image_open B
  continuousOn_toFun := B.map_smooth.continuousOn
  continuousOn_invFun := B.inverse_smooth.continuousOn


theorem surgeryBall_isImage_closedBall :
    (surgeryBallPartialHomeomorph B).IsImage (Metric.closedBall 0 1) B.closedBall := by
  intro x hx
  change B.map x ∈ B.closedBall ↔ x ∈ Metric.closedBall 0 1
  rw [surgeryBall_mem_closedBall_iff B (Set.mem_image_of_mem _ hx), B.left_inverse hx]
  simp only [Metric.mem_closedBall, dist_zero_right]


theorem surgeryBall_closedBall_interior :
    interior B.closedBall = B.map '' Metric.ball 0 1 := by
  have h := (surgeryBall_isImage_closedBall B).interior
  rw [interior_closedBall (0 : StandardCapSpace) (by norm_num : (1 : ℝ) ≠ 0)] at h
  apply Set.Subset.antisymm
  · intro y hy
    have hychart := surgeryBall_closedBall_subset_image B (interior_subset hy)
    obtain ⟨x, hx, rfl⟩ := hychart
    exact ⟨x, (h hx).mp hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (h (Metric.ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2) hx)).mpr hx


theorem surgeryBall_closedBall_frontier :
    frontier B.closedBall = B.map '' Metric.sphere 0 1 := by
  have h := (surgeryBall_isImage_closedBall B).frontier
  rw [frontier_closedBall (0 : StandardCapSpace) (by norm_num : (1 : ℝ) ≠ 0)] at h
  have hclosed : IsClosed B.closedBall :=
    (surgeryBall_closedImage_compact B 1 (by norm_num)).isClosed
  apply Set.Subset.antisymm
  · intro y hy
    have hychart := surgeryBall_closedBall_subset_image B (hclosed.frontier_subset hy)
    obtain ⟨x, hx, rfl⟩ := hychart
    exact ⟨x, (h hx).mp hy, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (h (Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2)
      (Metric.sphere_subset_closedBall hx))).mpr hx


theorem surgeryBall_closedBall_connected : IsConnected B.closedBall :=
  (Metric.isConnected_closedBall (by norm_num : (0 : ℝ) ≤ 1)).image _
    (B.map_smooth.continuousOn.mono (Metric.closedBall_subset_ball (by norm_num)))


theorem surgeryBall_frontier_connected : IsConnected (frontier B.closedBall) := by
  rw [surgeryBall_closedBall_frontier]
  exact (isConnected_sphere
    (Module.one_lt_rank_of_one_lt_finrank (by simp))
    (0 : StandardCapSpace) (zero_le_one : (0 : ℝ) ≤ 1)).image _
      (B.map_smooth.continuousOn.mono
        (Metric.sphere_subset_closedBall.trans (Metric.closedBall_subset_ball (by norm_num))))



theorem sphereBall_complement_connected
    (B : SurgeryBallEmbedding sphereCarrier.{u}) : IsConnected B.closedBallᶜ := by
  let E := sphereBallComplementEquivalence B
  rw [← E.inverse_image]
  have hE : IsConnected (Set.univ : Set euclideanCarrier.{u}.carrier) := by
    change IsConnected (Set.univ : Set (ULift.{u} StandardCapSpace))
    exact isConnected_univ
  exact hE.image _ E.inverse_smooth.continuousOn

end PoincareConjecture.M38
