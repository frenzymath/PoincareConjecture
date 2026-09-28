import PoincareConjecture.Proofs.M38.BallTransport
import PoincareConjecture.Proofs.M38.PairBallShrinking
import PoincareConjecture.Proofs.M38.TwoBallCenters










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38






theorem exists_two_ball_neighborhood {A : GeneralizedSliceCarrier.{u}}
    (B D : SurgeryBallEmbedding A)
    (hBD : Disjoint (B.map '' Metric.ball (0 : StandardCapSpace) 2)
      (D.map '' Metric.ball (0 : StandardCapSpace) 2))
    (hD : D.map 0 ∈ connectedComponent (B.map 0)) :
    ∃ C : SurgeryBallEmbedding A,
      B.map '' Metric.closedBall 0 (5 / 4) ∪
        D.map '' Metric.closedBall 0 (5 / 4) ⊆ C.map '' Metric.ball 0 1 := by
  classical
  let v : StandardCapSpace := EuclideanSpace.single (0 : Fin 3) (1 / 4 : ℝ)
  have hvnorm : ‖v‖ = 1 / 4 := by norm_num [v]
  have hv : v ∈ Metric.ball (0 : StandardCapSpace) 2 := by
    simp only [Metric.mem_ball, dist_zero_right, hvnorm]
    norm_num
  have hv0 : v ≠ 0 := by
    intro heq
    rw [heq, norm_zero] at hvnorm
    norm_num at hvnorm
  have hne : D.map 0 ≠ B.map 0 := by
    intro heq
    exact Set.disjoint_left.mp hBD
      (show B.map 0 ∈ B.map '' Metric.ball 0 2 from ⟨0, by simp, rfl⟩)
      (show B.map 0 ∈ D.map '' Metric.ball 0 2 from ⟨0, by simp, heq⟩)
  obtain ⟨e0, hfirst, hsecond, _⟩ :=
    exists_two_ball_centers_in_chart B D hD hne v hv hv0
  let B0 := transportSurgeryBall B e0
  let D0 := transportSurgeryBall D e0
  have hBD0 : Disjoint (B0.map '' Metric.ball (0 : StandardCapSpace) 2)
      (D0.map '' Metric.ball (0 : StandardCapSpace) 2) := by
    dsimp only [B0, D0]
    rw [transportSurgeryBall_image, transportSurgeryBall_image]
    exact Set.disjoint_image_of_injective e0.injective hBD
  let O : Set A.carrier := B.map '' Metric.ball (0 : StandardCapSpace) 1
  have hO : IsOpen O := surgeryBall_image_ball_open B 1 (by norm_num)
  have hB0 : B0.map 0 ∈ O := by
    change e0 (B.map 0) ∈ B.map '' Metric.ball 0 1
    rw [hfirst]
    exact ⟨0, by simp, rfl⟩
  have hD0 : D0.map 0 ∈ O := by
    change e0 (D.map 0) ∈ B.map '' Metric.ball 0 1
    rw [hsecond]
    refine ⟨v, ?_, rfl⟩
    simp only [Metric.mem_ball, dist_zero_right, hvnorm]
    norm_num
  obtain ⟨e1, c, d, _, _, _, _, _, _, himage, _⟩ :=
    exists_pairBallShrink_in_open B0 D0 hBD0 hO hB0 hD0
  let e := e0.trans e1
  refine ⟨transportSurgeryBall B e.symm, ?_⟩
  intro x hx
  have he0 : e0 x ∈ B0.map '' Metric.closedBall 0 (5 / 4) ∪
      D0.map '' Metric.closedBall 0 (5 / 4) := by
    rcases hx with ⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩
    · exact Or.inl ⟨z, hz, rfl⟩
    · exact Or.inr ⟨z, hz, rfl⟩
  have he : e x ∈ O := himage ⟨e0 x, he0, rfl⟩
  obtain ⟨z, hz, hmap⟩ := he
  refine ⟨z, hz, ?_⟩
  change e.symm (B.map z) = x
  rw [hmap, e.symm_apply_apply]

end PoincareConjecture.M38
