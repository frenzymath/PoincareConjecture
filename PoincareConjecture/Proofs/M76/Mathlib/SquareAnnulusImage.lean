import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusBlocks











set_option autoImplicit false

open Set

namespace PLAnnularStrip




theorem wrappedStripMap_image {L d : ℝ} (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    wrappedStripMap L '' rectangle (4 * L) d = squareAnnulus L d := by
  rw [← union_four_strips hd (show 2 * d < L by linarith)]
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, s, hs, he⟩ := exists_period_block hp.1
    have ht : 4 * |p.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
    have hbase : stripMap L (s, p.2) ∈ trapezoid L d := by
      rw [← stripMap_image hwidth]
      exact mem_image_of_mem _ (show (s, p.2) ∈ rectangle L d from ⟨hs, hp.2⟩)
    have hmem : stripRotation L i (stripMap L (s, p.2)) ∈ stripRegion L d i := by
      rw [← stripRotation_image]
      exact mem_image_of_mem _ hbase
    have hval : wrappedStripMap L p = stripRotation L i (stripMap L (s, p.2)) := by
      calc
        wrappedStripMap L p = wrappedStripMap L (p.1, p.2) := rfl
        _ = wrappedStripMap L (s + (i.val : ℝ) * L, p.2) := by rw [he]
        _ = _ := wrappedStripMap_block ht hs i
    rw [hval]
    fin_cases i
    · exact Or.inl (Or.inl (Or.inl hmem))
    · exact Or.inl (Or.inl (Or.inr hmem))
    · exact Or.inl (Or.inr hmem)
    · exact Or.inr hmem
  · intro hx
    have hi : ∃ i : Fin 4, x ∈ stripRegion L d i := by
      rcases hx with (((hx | hx) | hx) | hx)
      · exact ⟨0, hx⟩
      · exact ⟨1, hx⟩
      · exact ⟨2, hx⟩
      · exact ⟨3, hx⟩
    obtain ⟨i, hi⟩ := hi
    have hpre : x ∈ (stripRotation L i ∘ stripMap L) '' rectangle L d := by
      rw [image_comp, stripMap_image hwidth, stripRotation_image]
      exact hi
    obtain ⟨p, hp, hval⟩ := hpre
    have ht : 4 * |p.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
    refine ⟨(p.1 + (i.val : ℝ) * L, p.2), ⟨?_, hp.2⟩,
      (wrappedStripMap_block ht hp.1 i).trans hval⟩
    have hlo : 0 ≤ p.1 := hp.1.1
    have hhi : p.1 ≤ L := hp.1.2
    fin_cases i <;> dsimp <;> norm_num <;> constructor <;> linarith





theorem range_annulusMap {L d : ℝ} (hL : 0 < L) (hd : 0 ≤ d) (hwidth : 4 * d < L) :
    range (fun p : AddCircle (4 * L) × Icc (-d) d => annulusMap L hL (p.1, p.2)) =
      squareAnnulus L d := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  ext x
  constructor
  · rintro ⟨⟨z, t⟩, rfl⟩
    let s : ℝ := AddCircle.equivIco (4 * L) 0 z
    have hs : s ∈ Icc 0 (4 * L) := by
      have h := (AddCircle.equivIco (4 * L) 0 z).property
      exact ⟨h.1, by simpa only [zero_add] using h.2.le⟩
    have hcoe : (s : AddCircle (4 * L)) = z := AddCircle.coe_equivIco
    have ht : 4 * |(t : ℝ)| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr t.property) (by norm_num)) hwidth
    change annulusMap L hL (z, t) ∈ squareAnnulus L d
    rw [← hcoe, annulusMap_coe hL ht hs, ← wrappedStripMap_image hd hwidth]
    exact mem_image_of_mem _ (show (s, (t : ℝ)) ∈ rectangle (4 * L) d from ⟨hs, t.property⟩)
  · intro hx
    rw [← wrappedStripMap_image hd hwidth] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    have ht : 4 * |p.2| < L :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2) (by norm_num)) hwidth
    exact ⟨((p.1 : AddCircle (4 * L)), ⟨p.2, hp.2⟩), annulusMap_coe hL ht hp.1⟩

end PLAnnularStrip
