import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusParametrization











set_option autoImplicit false

open Set

namespace PLAnnularStrip

private theorem wrappedStripMap_bottom {L s t : ℝ} (hs : s ∈ Icc 0 L) :
    wrappedStripMap L (s, t) = (coordinate L s t, t) := by
  simp only [wrappedStripMap, hs.2, if_true]

private theorem wrappedStripMap_right {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    wrappedStripMap L (s + L, t) = (L - t, coordinate L s t) := by
  have hL : 0 < L := by linarith [abs_nonneg t]
  by_cases hs0 : s = 0
  · subst s
    simp only [zero_add, wrappedStripMap, le_refl, if_true,
      (coordinate_endpoints ht).1, (coordinate_endpoints ht).2]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have h₁ : ¬ s + L ≤ L := by linarith
    have h₂ : s + L ≤ 2 * L := by linarith [hs.2]
    simp only [wrappedStripMap, h₁, h₂, if_false, if_true, add_sub_cancel_right]

private theorem wrappedStripMap_top {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    wrappedStripMap L (s + 2 * L, t) = (L - coordinate L s t, L - t) := by
  have hL : 0 < L := by linarith [abs_nonneg t]
  have h₁ : ¬ s + 2 * L ≤ L := by linarith [hs.1]
  by_cases hs0 : s = 0
  · subst s
    have h₂ : (0 : ℝ) + 2 * L ≤ 2 * L := by linarith
    have hsub : (0 : ℝ) + 2 * L - L = L := by ring
    simp only [wrappedStripMap, h₁, h₂, if_false, if_true, hsub,
      (coordinate_endpoints ht).1, (coordinate_endpoints ht).2]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have h₂ : ¬ s + 2 * L ≤ 2 * L := by linarith
    have h₃ : s + 2 * L ≤ 3 * L := by linarith [hs.2]
    simp only [wrappedStripMap, h₁, h₂, h₃, if_false, if_true, add_sub_cancel_right]

private theorem wrappedStripMap_left {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) :
    wrappedStripMap L (s + 3 * L, t) = (t, L - coordinate L s t) := by
  have hL : 0 < L := by linarith [abs_nonneg t]
  have h₁ : ¬ s + 3 * L ≤ L := by linarith [hs.1]
  have h₂ : ¬ s + 3 * L ≤ 2 * L := by linarith [hs.1]
  by_cases hs0 : s = 0
  · subst s
    have h₃ : (0 : ℝ) + 3 * L ≤ 3 * L := by linarith
    have hsub : (0 : ℝ) + 3 * L - 2 * L = L := by ring
    simp only [wrappedStripMap, h₁, h₂, h₃, if_false, if_true, hsub,
      (coordinate_endpoints ht).1, (coordinate_endpoints ht).2, sub_sub_cancel]
  · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
    have h₃ : ¬ s + 3 * L ≤ 3 * L := by linarith
    simp only [wrappedStripMap, h₁, h₂, h₃, if_false, add_sub_cancel_right]




theorem wrappedStripMap_block {L s t : ℝ}
    (ht : 4 * |t| < L) (hs : s ∈ Icc 0 L) (i : Fin 4) :
    wrappedStripMap L (s + (i.val : ℝ) * L, t) =
      stripRotation L i (stripMap L (s, t)) := by
  fin_cases i
  · simpa [stripRotation, stripMap] using wrappedStripMap_bottom (t := t) hs
  · simpa [stripRotation, stripMap] using wrappedStripMap_right ht hs
  · simpa [stripRotation, stripMap] using wrappedStripMap_top ht hs
  · simpa [stripRotation, stripMap] using wrappedStripMap_left ht hs




theorem exists_period_block {L s : ℝ} (hs : s ∈ Icc 0 (4 * L)) :
    ∃ i : Fin 4, ∃ r ∈ Icc 0 L, s = r + (i.val : ℝ) * L := by
  by_cases h₁ : s ≤ L
  · exact ⟨0, s, ⟨hs.1, h₁⟩, by simp⟩
  by_cases h₂ : s ≤ 2 * L
  · refine ⟨1, s - L, ⟨by linarith, by linarith⟩, ?_⟩
    norm_num
  by_cases h₃ : s ≤ 3 * L
  · refine ⟨2, s - 2 * L, ⟨by linarith, by linarith⟩, ?_⟩
    norm_num
  · refine ⟨3, s - 3 * L, ⟨by linarith, by linarith [hs.2]⟩, ?_⟩
    norm_num

end PLAnnularStrip
