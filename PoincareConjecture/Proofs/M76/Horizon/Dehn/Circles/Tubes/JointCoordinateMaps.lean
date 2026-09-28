import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.JointDiamondMap
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.SignedAxisPermutations









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem signedTubeQuarter_side_iff (b c : Bool) (x : signedTubeDiamond) :
    (x : P2) ∈ signedTubeQuarter b c ↔
      SignedJointCross.side b x.val.1 ∧ SignedJointCross.side c x.val.2 := by
  have hside (b : Bool) (u : ℝ) :
      0 ≤ (if b then u else -u) ↔ SignedJointCross.side b u := by
    cases b <;> simp [SignedJointCross.side]
  have hbound (b : Bool) (u : ℝ) : (if b then u else -u) ≤ |u| := by
    cases b
    exacts [neg_le_abs u, le_abs_self u]
  rw [signedTubeQuarter_coordinate_iff, hside, hside]
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2,
    (add_le_add (hbound b x.val.1) (hbound c x.val.2)).trans
      ((signedTubeDiamond_coordinate_iff x).mp x.property)⟩⟩

namespace SignedJointCross

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (J : SignedJointCross E)

omit [FiniteDimensional ℝ E] in
theorem diamond_map_coordinate_sides (G : signedTubeDiamond ≃ₜ J.disk)
    (hquarter : ∀ b c (x : signedTubeDiamond),
      (x : P2) ∈ signedTubeQuarter b c ↔ (G x : E) ∈ J.quarter b c) :
    ∀ j b (x : signedTubeDiamond),
      side b (SignedAxisPermutation.coordinate j x) ↔ side b (J.coordinate j (G x)) := by
  have hex (u : ℝ) : ∃ b, side b u := by
    rcases le_total 0 u with h | h
    exacts [⟨true, h⟩, ⟨false, h⟩]
  intro j b x
  fin_cases j
  · change side b x.val.1 ↔ side b (J.coordinate 0 (G x))
    constructor
    · intro h
      obtain ⟨c, hc⟩ := hex x.val.2
      exact ((hquarter b c x).mp ((signedTubeQuarter_side_iff b c x).mpr ⟨h, hc⟩)).2.1
    · intro h
      obtain ⟨c, hc⟩ := hex (J.coordinate 1 (G x))
      exact ((signedTubeQuarter_side_iff b c x).mp
        ((hquarter b c x).mpr ⟨(G x).property, h, hc⟩)).1
  · change side b x.val.2 ↔ side b (J.coordinate 1 (G x))
    constructor
    · intro h
      obtain ⟨c, hc⟩ := hex x.val.1
      exact ((hquarter c b x).mp ((signedTubeQuarter_side_iff c b x).mpr ⟨hc, h⟩)).2.2
    · intro h
      obtain ⟨c, hc⟩ := hex (J.coordinate 0 (G x))
      exact ((signedTubeQuarter_side_iff c b x).mp
        ((hquarter c b x).mpr ⟨(G x).property, hc, h⟩)).2

theorem exists_diamond_map_with_sides :
    ∃ G : signedTubeDiamond ≃ₜ J.disk, G.IsFinitePL ∧
      (∀ j b (x : signedTubeDiamond),
        side b (SignedAxisPermutation.coordinate j x) ↔ side b (J.coordinate j (G x))) ∧
      (∀ j (x : signedTubeDiamond),
        (x : P2) ∈ signedTubeSheet j ↔ (G x : E) ∈ J.axis j) ∧
      (G ⟨(0, 0), mem_iUnion.mpr ⟨false, mem_iUnion.mpr ⟨false, signedTube_center_mem⟩⟩⟩ : E) =
        J.center ∧
      ∀ j b, (G ⟨signedTubeCorner j b,
        signedTubeRadius_subset_diamond j b (right_mem_segment ℝ _ _)⟩ : E) = J.endpoint j b := by
  obtain ⟨G, hG, hquarter, hsheet, hcenter, hcorner⟩ := J.exists_diamond_map
  exact ⟨G, hG, J.diamond_map_coordinate_sides G hquarter, hsheet, hcenter, hcorner⟩

end SignedJointCross
end PoincareConjecture.M76.Dehn
