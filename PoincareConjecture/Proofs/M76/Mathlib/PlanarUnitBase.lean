import PoincareConjecture.Proofs.M76.Mathlib.PlanarCapTopEdge










set_option autoImplicit false

open Set

namespace PlanarSegment




theorem unit_base_subset_of_inter {a b q : ℝ × ℝ}
    (ha : a.1 + a.2 = 1) (hb : b.1 + b.2 = 1)
    (hapos : ¬ (0 < a.1 ∧ 0 < a.2)) (hbpos : ¬ (0 < b.1 ∧ 0 < b.2))
    (hq : q ∈ segment ℝ a b) (hqx : 0 < q.1) (hqy : 0 < q.2)
    (hqh : q.1 + q.2 = 1) : segment ℝ (1, 0) (0, 1) ⊆ segment ℝ a b := by
  have hqa := (Prod.segment_subset (𝕜 := ℝ) a b hq).1
  rw [segment_eq_uIcc] at hqa
  have haout : a.1 ≤ 0 ∨ 1 ≤ a.1 := by
    by_cases h : a.1 ≤ 0
    · exact Or.inl h
    · right
      have h2 : a.2 ≤ 0 := le_of_not_gt (fun h2 => hapos ⟨lt_of_not_ge h, h2⟩)
      linarith
  have hbout : b.1 ≤ 0 ∨ 1 ≤ b.1 := by
    by_cases h : b.1 ≤ 0
    · exact Or.inl h
    · right
      have h2 : b.2 ≤ 0 := le_of_not_gt (fun h2 => hbpos ⟨lt_of_not_ge h, h2⟩)
      linarith
  have hbounds : min a.1 b.1 ≤ 0 ∧ 1 ≤ max a.1 b.1 := by
    rcases haout with hal | har <;> rcases hbout with hbl | hbr
    · exact (not_le_of_gt hqx (hqa.2.trans (max_le hal hbl))).elim
    · exact ⟨(min_le_left _ _).trans hal, hbr.trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans hbl, har.trans (le_max_left _ _)⟩
    · have h1 : 1 ≤ q.1 := (le_min har hbr).trans hqa.1
      linarith
  let f : ℝ →ᵃ[ℝ] ℝ × ℝ := AffineMap.lineMap (0, 1) (1, 0)
  have hfa : f a.1 = a := by
    rw [show f a.1 = a.1 • ((1, 0) - (0, 1)) + (0, 1) from
      AffineMap.lineMap_apply_module' _ _ _]
    apply Prod.ext
    · change a.1 * (1 - 0) + 0 = a.1
      ring
    · change a.1 * (0 - 1) + 1 = a.2
      linarith
  have hfb : f b.1 = b := by
    rw [show f b.1 = b.1 • ((1, 0) - (0, 1)) + (0, 1) from
      AffineMap.lineMap_apply_module' _ _ _]
    apply Prod.ext
    · change b.1 * (1 - 0) + 0 = b.1
      ring
    · change b.1 * (0 - 1) + 1 = b.2
      linarith
  have himage : f '' segment ℝ a.1 b.1 = segment ℝ a b := by
    rw [image_segment, hfa, hfb]
  have hzero : ((0, 1) : ℝ × ℝ) ∈ segment ℝ a b := by
    rw [← himage]
    refine ⟨0, ?_, AffineMap.lineMap_apply_zero _ _⟩
    rw [segment_eq_uIcc]
    exact ⟨hbounds.1, zero_le_one.trans hbounds.2⟩
  have hone : ((1, 0) : ℝ × ℝ) ∈ segment ℝ a b := by
    rw [← himage]
    refine ⟨1, ?_, AffineMap.lineMap_apply_one _ _⟩
    rw [segment_eq_uIcc]
    exact ⟨hbounds.1.trans zero_le_one, hbounds.2⟩
  exact (convex_segment (𝕜 := ℝ) a b).segment_subset hone hzero

end PlanarSegment
