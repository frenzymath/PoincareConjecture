import PoincareConjecture.Proofs.M38.BallGermRectification
import PoincareConjecture.Proofs.M38.BallShrinking
import PoincareConjecture.Proofs.M38.BallTransport










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M38

variable {A : GeneralizedSliceCarrier.{u}}





theorem exists_surgeryBallAffineNormalizationCompact (B C : SurgeryBallEmbedding A)
    (hBC : B.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b : ℝ,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => C.inverse (B.map x)) 0 ∧
      0 < b ∧ b < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        e (B.map x) = C.map (C.inverse (B.map 0) + L (b • x))) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        C.inverse (B.map 0) + L (b • x) ∈ Metric.ball 0 2) ∧
      (∀ y : A.carrier, y ∉ B.map '' Metric.closedBall 0 (3 / 2) → e y = y) := by
  obtain ⟨L, hL, r, hr, E, hE, hEfix⟩ :=
    exists_surgeryBallGermRectification B C hBC
      (surgeryBall_image_ball_open B 1 (by norm_num))
      (show B.map 0 ∈ B.map '' Metric.ball 0 1 from ⟨0, by simp, rfl⟩)
  let f : StandardCapSpace → StandardCapSpace :=
    fun x => C.inverse (B.map 0) + L x
  have hf : Continuous f := continuous_const.add L.continuous
  have hf0 : f 0 ∈ Metric.ball (0 : StandardCapSpace) 2 := by
    simpa only [f, map_zero, add_zero] using surgeryBall_inverse_mem C hBC
  obtain ⟨t, ht, hball⟩ := Metric.mem_nhds_iff.mp
    (hf.continuousAt.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds hf0))
  obtain ⟨s, b, hb, hb1, hbsmall, hs, _, hsfix, _⟩ :=
    exists_surgeryBallShrink B (min r t) (lt_min hr ht)
  have hscaled (x : StandardCapSpace) (hx : ‖x‖ ≤ 5 / 4) :
      ‖b • x‖ < min r t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hb]
    exact (mul_le_mul_of_nonneg_left hx hb.le).trans_lt hbsmall
  refine ⟨s.trans E, L, b, hL, hb, hb1, ?_, ?_, ?_⟩
  · intro x hx
    change E (s (B.map x)) = C.map (C.inverse (B.map 0) + L (b • x))
    rw [hs x hx]
    exact hE (b • x) ((hscaled x hx).trans_le (min_le_left r t))
  · intro x hx
    change f (b • x) ∈ Metric.ball 0 2
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right] using
      (hscaled x hx).trans_le (min_le_right r t)
  · intro y hy
    change E (s y) = y
    have hsmall : y ∉ B.map '' Metric.ball 0 1 := by
      intro hmem
      exact hy ((Set.image_mono
        (Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall
          (by norm_num)))) hmem)
    rw [hsfix y hy, hEfix y hsmall]



theorem exists_surgeryBallAffineNormalization (B C : SurgeryBallEmbedding A)
    (hBC : B.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    ∃ L : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b : ℝ,
      (L : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => C.inverse (B.map x)) 0 ∧
      0 < b ∧ b < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        e (B.map x) = C.map (C.inverse (B.map 0) + L (b • x))) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        C.inverse (B.map 0) + L (b • x) ∈ Metric.ball 0 2) ∧
      (∀ y : A.carrier, y ∉ B.map '' Metric.ball 0 2 → e y = y) := by
  obtain ⟨e, L, b, hL, hb, hb1, hinner, hcoord, hfix⟩ :=
    exists_surgeryBallAffineNormalizationCompact B C hBC
  refine ⟨e, L, b, hL, hb, hb1, hinner, hcoord, ?_⟩
  intro y hy
  exact hfix y (fun h => hy ((Set.image_mono
    (Metric.closedBall_subset_ball (by norm_num))) h))







theorem exists_twoBallAffineNormalization (B D C : SurgeryBallEmbedding A)
    (hBD : Disjoint (B.map '' Metric.ball (0 : StandardCapSpace) 2)
      (D.map '' Metric.ball (0 : StandardCapSpace) 2))
    (hBC : B.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2)
    (hDC : D.map 0 ∈ C.map '' Metric.ball (0 : StandardCapSpace) 2) :
    ∃ e : Diffeomorph (𝓡 3) (𝓡 3) A.carrier A.carrier ∞,
    ∃ LB LD : StandardCapSpace ≃L[ℝ] StandardCapSpace,
    ∃ b d : ℝ,
      (LB : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => C.inverse (B.map x)) 0 ∧
      (LD : StandardCapSpace →L[ℝ] StandardCapSpace) =
        fderiv ℝ (fun x => C.inverse (D.map x)) 0 ∧
      0 < b ∧ b < 1 ∧ 0 < d ∧ d < 1 ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        e (B.map x) = C.map (C.inverse (B.map 0) + LB (b • x))) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        e (D.map x) = C.map (C.inverse (D.map 0) + LD (d • x))) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        C.inverse (B.map 0) + LB (b • x) ∈ Metric.ball 0 2) ∧
      (∀ x : StandardCapSpace, ‖x‖ ≤ 5 / 4 →
        C.inverse (D.map 0) + LD (d • x) ∈ Metric.ball 0 2) ∧
      (∀ y : A.carrier,
        y ∉ B.map '' Metric.ball 0 2 ∪ D.map '' Metric.ball 0 2 → e y = y) ∧
      (∀ y : A.carrier,
        y ∉ B.map '' Metric.ball 0 2 ∪ D.map '' Metric.ball 0 2 → e.symm y = y) := by
  obtain ⟨eB, LB, b, hLB, hb, hb1, heB, hcoordB, hfixB⟩ :=
    exists_surgeryBallAffineNormalization B C hBC
  obtain ⟨eD, LD, d, hLD, hd, hd1, heD, hcoordD, hfixD⟩ :=
    exists_surgeryBallAffineNormalization D C hDC
  have hpreserveB {y : A.carrier} (hy : y ∈ B.map '' Metric.ball 0 2) :
      eB y ∈ B.map '' Metric.ball 0 2 := by
    by_contra hnot
    have heq : eB y = y := eB.injective (hfixB (eB y) hnot)
    exact hnot (heq.symm ▸ hy)
  let e := eB.trans eD
  have hfix (y : A.carrier)
      (hy : y ∉ B.map '' Metric.ball 0 2 ∪ D.map '' Metric.ball 0 2) : e y = y := by
    change eD (eB y) = y
    rw [hfixB y (fun h => hy (Or.inl h)), hfixD y (fun h => hy (Or.inr h))]
  refine ⟨e, LB, LD, b, d, hLB, hLD, hb, hb1, hd, hd1,
    ?_, ?_, hcoordB, hcoordD, hfix, ?_⟩
  · intro x hx
    have hxball : x ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    have hout : eB (B.map x) ∉ D.map '' Metric.ball 0 2 := by
      intro hmem
      exact Set.disjoint_left.mp hBD
        (hpreserveB (Set.mem_image_of_mem B.map hxball)) hmem
    change eD (eB (B.map x)) = C.map (C.inverse (B.map 0) + LB (b • x))
    rw [hfixD _ hout, heB x hx]
  · intro x hx
    have hxball : x ∈ Metric.ball (0 : StandardCapSpace) 2 := by
      simp only [Metric.mem_ball, dist_zero_right]
      linarith
    have hout : D.map x ∉ B.map '' Metric.ball 0 2 := by
      intro hmem
      exact Set.disjoint_left.mp hBD hmem (Set.mem_image_of_mem D.map hxball)
    change eD (eB (D.map x)) = C.map (C.inverse (D.map 0) + LD (d • x))
    rw [hfixB _ hout, heD x hx]
  · intro y hy
    apply e.injective
    change e (e.symm y) = e y
    rw [e.apply_symm_apply, hfix y hy]

end PoincareConjecture.M38
