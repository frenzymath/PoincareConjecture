import PoincareConjecture.Proofs.M38.BallShrinking









set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}



theorem exists_surgeryBall_radius_in_open (B : SurgeryBallEmbedding A)
    {O : Set A.carrier} (hO : IsOpen O) (hp : B.map 0 ∈ O) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ B.map '' Metric.ball 0 r ⊆ O := by
  have hc : ContinuousAt B.map 0 :=
    (B.map_smooth.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp))).continuousAt
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (hc.preimage_mem_nhds (hO.mem_nhds hp))
  refine ⟨min r 1, lt_min hr (by norm_num), min_le_right _ _, ?_⟩
  rintro y ⟨x, hx, rfl⟩
  exact hball (Metric.ball_subset_ball (min_le_left r 1) hx)



theorem exists_pairBallShrink_in_open (B D : SurgeryBallEmbedding A)
    (hBD : Disjoint (B.map '' Metric.ball (0 : StandardCapSpace) 2)
      (D.map '' Metric.ball (0 : StandardCapSpace) 2))
    {O : Set A.carrier} (hO : IsOpen O) (hB : B.map 0 ∈ O) (hD : D.map 0 ∈ O) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    ∃ c d : ℝ, 0 < c ∧ c < 1 ∧ 0 < d ∧ d < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 → e (B.map x) = B.map (c • x)) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 → e (D.map x) = D.map (d • x)) ∧
      e '' (B.map '' Metric.closedBall 0 (5 / 4) ∪
        D.map '' Metric.closedBall 0 (5 / 4)) ⊆ O ∧
      (∀ x : A.carrier, x ∉ B.map '' Metric.closedBall 0 (3 / 2) ∪
        D.map '' Metric.closedBall 0 (3 / 2) → e x = x) := by
  obtain ⟨r, hr, hr1, hrO⟩ := exists_surgeryBall_radius_in_open B hO hB
  obtain ⟨s, hs, hs1, hsO⟩ := exists_surgeryBall_radius_in_open D hO hD
  obtain ⟨eB, c, hc, hc1, _, heB, himB, hfixB, _⟩ := exists_surgeryBallShrink B r hr
  obtain ⟨eD, d, hd, hd1, _, heD, himD, hfixD, _⟩ := exists_surgeryBallShrink D s hs
  have hBoffD {x : A.carrier} (hx : x ∈ B.map '' Metric.ball 0 2) :
      x ∉ D.map '' Metric.closedBall 0 (3 / 2) := by
    intro hxD
    exact Set.disjoint_left.mp hBD hx
      ((Set.image_mono (Metric.closedBall_subset_ball (by norm_num))) hxD)
  have hDoffB {x : A.carrier} (hx : x ∈ D.map '' Metric.ball 0 2) :
      x ∉ B.map '' Metric.closedBall 0 (3 / 2) := by
    intro hxB
    exact Set.disjoint_left.mp hBD
      ((Set.image_mono (Metric.closedBall_subset_ball (by norm_num))) hxB) hx
  let e := eB.trans eD
  refine ⟨e, c, d, hc, hc1, hd, hd1, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hcx : c • x ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simp only [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
      nlinarith [norm_nonneg x]
    change eD (eB (B.map x)) = B.map (c • x)
    rw [heB x hx, hfixD _ (hBoffD (Set.mem_image_of_mem B.map hcx))]
  · intro x hx
    have hxball : x ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    change eD (eB (D.map x)) = D.map (d • x)
    rw [hfixB _ (hDoffB (Set.mem_image_of_mem D.map hxball)), heD x hx]
  · rintro y ⟨x, hx, rfl⟩
    change eD (eB x) ∈ O
    rcases hx with hx | hx
    · have heBx := himB (Set.mem_image_of_mem eB hx)
      have heBfull : eB x ∈ B.map '' Metric.ball (0 : StandardCapSpace) 2 :=
        (Set.image_mono (Metric.ball_subset_ball (hr1.trans (by norm_num)))) heBx
      rw [hfixD _ (hBoffD heBfull)]
      exact hrO heBx
    · have hxfull : x ∈ D.map '' Metric.ball (0 : StandardCapSpace) 2 :=
        (Set.image_mono (Metric.closedBall_subset_ball (by norm_num))) hx
      rw [hfixB _ (hDoffB hxfull)]
      exact hsO (himD (Set.mem_image_of_mem eD hx))
  · intro x hx
    change eD (eB x) = x
    rw [hfixB x (fun h => hx (Or.inl h)), hfixD x (fun h => hx (Or.inr h))]

end PoincareConjecture.M38
