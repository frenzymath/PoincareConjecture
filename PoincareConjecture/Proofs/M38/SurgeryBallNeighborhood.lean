import PoincareConjecture.Proofs.M38.SurgeryBallTopology
import PoincareConjecture.Proofs.M38.AnnulusReparametrization
import PoincareConjecture.Proofs.M38.CapBallEmbedding
import PoincareConjecture.Proofs.M38.FiniteBallNeighborhoods

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

theorem exists_surgeryBall_with_image_in_open
    {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
    {U : Set A.carrier} (hU : IsOpen U) (hBU : B.closedBall ⊆ U) :
    ∃ D : SurgeryBallEmbedding A,
      D.closedBall = B.closedBall ∧ D.map 0 = B.map 0 ∧
        D.map '' Metric.ball 0 2 ⊆ U := by
  let V : Set StandardCapSpace := Metric.ball 0 2 ∩ B.map ⁻¹' U
  have hV : IsOpen V :=
    (surgeryBallPartialHomeomorph B).isOpen_inter_preimage hU
  have hBV : Metric.closedBall (0 : StandardCapSpace) 1 ⊆ V := by
    intro x hx
    exact ⟨Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hx,
      hBU (Set.mem_image_of_mem _ hx)⟩
  obtain ⟨a, ha, ha1, haV⟩ := exists_cap_ball_width (by norm_num : (0 : ℝ) < 1) hV hBV
  refine ⟨annulusReparametrizedBall ha ha1 B,
    annulusReparametrizedBall_closedBall ha ha1 B,
    annulusReparametrizedBall_center ha ha1 B, ?_⟩
  rw [annulusReparametrizedBall_image]
  rintro _ ⟨x, hx, rfl⟩
  exact (haV hx).2

theorem exists_surgeryBall_with_disjoint_finite_images
    {A : GeneralizedSliceCarrier.{u}} (B : SurgeryBallEmbedding A)
    {I : Type*} [Finite I] (f : I → A.carrier → A.carrier)
    (hf : ∀ i, Continuous (f i))
    (hdisjoint : ∀ i, Disjoint B.closedBall (f i '' B.closedBall)) :
    ∃ D : SurgeryBallEmbedding A,
      D.closedBall = B.closedBall ∧ D.map 0 = B.map 0 ∧
        ∀ i, Disjoint (D.map '' Metric.ball 0 2)
          (f i '' (D.map '' Metric.ball 0 2)) := by
  obtain ⟨U, hU, hBU, hsep⟩ := exists_open_disjoint_finite_images_of_compact
    (surgeryBall_closedImage_compact B 1 (by norm_num)) f hf hdisjoint
  obtain ⟨D, hD, hcenter, hDU⟩ := exists_surgeryBall_with_image_in_open B hU hBU
  exact ⟨D, hD, hcenter, fun i => (hsep i).mono hDU (Set.image_mono hDU)⟩

end PoincareConjecture.M38
