import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Tactic.Linarith










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D



def unitCorner : Set (ℝ × ℝ) :=
  segment ℝ (0, 0) (1, 0) ∪ segment ℝ (0, 0) (0, 1)



theorem mem_unitCorner_iff (z : ℝ × ℝ) :
    z ∈ unitCorner ↔
      (0 ≤ z.1 ∧ z.1 ≤ 1 ∧ z.2 = 0) ∨ (z.1 = 0 ∧ 0 ≤ z.2 ∧ z.2 ≤ 1) := by
  rw [unitCorner, mem_union, segment_eq_image, segment_eq_image]
  constructor
  · rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · left
      simpa using And.intro ht.1 (And.intro ht.2 (rfl : (0 : ℝ) = 0))
    · right
      simpa using And.intro (rfl : (0 : ℝ) = 0) ht
  · rintro (⟨hz0, hz1, hz2⟩ | ⟨hz1, hz0, hz2⟩)
    · left
      refine ⟨z.1, ⟨hz0, hz1⟩, ?_⟩
      ext <;> simp [hz2]
    · right
      refine ⟨z.2, ⟨hz0, hz2⟩, ?_⟩
      ext <;> simp [hz1]



theorem unitCorner_box_sectors {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    let W : Set (ℝ × ℝ) := Ioo (-r) r ×ˢ Ioo (-r) r
    let A : Set (ℝ × ℝ) := Ioo 0 r ×ˢ Ioo 0 r
    let B : Set (ℝ × ℝ) :=
      (Ioo (-r) 0 ×ˢ Ioo (-r) r) ∪ (Ioo (-r) r ×ˢ Ioo (-r) 0)
    IsOpen W ∧ (0, 0) ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
      A ∪ B = W \ unitCorner := by
  dsimp only
  have hneg : -r < 0 := neg_neg_of_pos hr
  have hmid : -r < -r / 2 ∧ -r / 2 < 0 := by constructor <;> linarith
  refine ⟨isOpen_Ioo.prod isOpen_Ioo, ⟨⟨hneg, hr⟩, hneg, hr⟩,
    ((convex_Ioo (𝕜 := ℝ) 0 r).prod (convex_Ioo 0 r)).isPreconnected, ?_, ?_⟩
  · apply IsPreconnected.union' (s := Ioo (-r) 0 ×ˢ Ioo (-r) r)
      (t := Ioo (-r) r ×ˢ Ioo (-r) 0)
    · exact ⟨(-r / 2, -r / 2), ⟨hmid, hmid.1, hmid.2.trans hr⟩,
        ⟨⟨hmid.1, hmid.2.trans hr⟩, hmid⟩⟩
    · exact ((convex_Ioo (𝕜 := ℝ) (-r) 0).prod (convex_Ioo (-r) r)).isPreconnected
    · exact ((convex_Ioo (𝕜 := ℝ) (-r) r).prod (convex_Ioo (-r) 0)).isPreconnected
  · ext z
    constructor
    · rintro (hz | hz | hz)
      · refine ⟨⟨⟨hneg.trans hz.1.1, hz.1.2⟩, hneg.trans hz.2.1, hz.2.2⟩, ?_⟩
        rw [mem_unitCorner_iff]
        rintro (hc | hc)
        · exact hz.2.1.ne' hc.2.2
        · exact hz.1.1.ne' hc.1
      · refine ⟨⟨⟨hz.1.1, hz.1.2.trans hr⟩, hz.2⟩, ?_⟩
        rw [mem_unitCorner_iff]
        rintro (hc | hc)
        · exact (not_le_of_gt hz.1.2) hc.1
        · exact hz.1.2.ne hc.1
      · refine ⟨⟨hz.1, hz.2.1, hz.2.2.trans hr⟩, ?_⟩
        rw [mem_unitCorner_iff]
        rintro (hc | hc)
        · exact hz.2.2.ne hc.2.2
        · exact (not_le_of_gt hz.2.2) hc.2.1
    · rintro ⟨hz, hc⟩
      by_cases hx : z.1 < 0
      · exact Or.inr (Or.inl ⟨⟨hz.1.1, hx⟩, hz.2⟩)
      by_cases hy : z.2 < 0
      · exact Or.inr (Or.inr ⟨hz.1, hz.2.1, hy⟩)
      have hx0 : 0 ≤ z.1 := le_of_not_gt hx
      have hy0 : 0 ≤ z.2 := le_of_not_gt hy
      have hxn : z.1 ≠ 0 := by
        intro heq
        exact hc ((mem_unitCorner_iff z).mpr (Or.inr ⟨heq, hy0, hz.2.2.le.trans hr1⟩))
      have hyn : z.2 ≠ 0 := by
        intro heq
        exact hc ((mem_unitCorner_iff z).mpr (Or.inl ⟨hx0, hz.1.2.le.trans hr1, heq⟩))
      exact Or.inl ⟨⟨lt_of_le_of_ne hx0 hxn.symm, hz.1.2⟩,
        lt_of_le_of_ne hy0 hyn.symm, hz.2.2⟩

end PoincareConjecture.M25.Topology3D
