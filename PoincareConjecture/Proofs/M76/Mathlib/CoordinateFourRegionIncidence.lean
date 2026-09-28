import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

open Set

namespace CoordinateFourRegions

def weakSign (i : Bool) (r : ℝ) : Prop := if i then r ≤ 0 else 0 ≤ r

def arc (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool × Bool) : Set ((ℝ × ℝ) × ℝ) :=
  F ∩ {x | if i.1 then x.2 = 0 ∧ weakSign i.2 x.1.1
    else x.1.1 = 0 ∧ weakSign i.2 x.2}

def region (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool × Bool) : Set ((ℝ × ℝ) × ℝ) :=
  F ∩ {x | weakSign i.1 x.1.1 ∧ weakSign i.2 x.2}

def graph (F : Set ((ℝ × ℝ) × ℝ)) : Set ((ℝ × ℝ) × ℝ) :=
  F ∩ ({x | x.1.1 = 0} ∪ {x | x.2 = 0})

private theorem weakSign_zero (i : Bool) : weakSign i 0 := by
  cases i <;> exact le_rfl

private theorem zero_of_different_signs {i j : Bool} (hij : i ≠ j) {r : ℝ}
    (hi : weakSign i r) (hj : weakSign j r) : r = 0 := by
  cases i <;> cases j
  · exact (hij rfl).elim
  · exact le_antisymm hj hi
  · exact le_antisymm hi hj
  · exact (hij rfl).elim

private theorem axis_subset_arc (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool × Bool) :
    F ∩ {x | x.1.1 = 0 ∧ x.2 = 0} ⊆ arc F i := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  rcases i with ⟨i, j⟩
  cases i
  · exact ⟨hx.2.1, hx.2.2 ▸ weakSign_zero j⟩
  · exact ⟨hx.2.2, hx.2.1 ▸ weakSign_zero j⟩

theorem arc_inter_of_ne (F : Set ((ℝ × ℝ) × ℝ)) {i j : Bool × Bool}
    (hij : i ≠ j) : arc F i ∩ arc F j = F ∩ {x | x.1.1 = 0 ∧ x.2 = 0} := by
  apply Subset.antisymm
  · rintro x ⟨hx, hy⟩
    refine ⟨hx.1, ?_⟩
    rcases i with ⟨i₀, i₁⟩
    rcases j with ⟨j₀, j₁⟩
    cases i₀ <;> cases j₀
    · have hside : i₁ ≠ j₁ := fun h => hij (Prod.ext rfl h)
      exact ⟨hx.2.1, zero_of_different_signs hside hx.2.2 hy.2.2⟩
    · exact ⟨hx.2.1, hy.2.1⟩
    · exact ⟨hy.2.1, hx.2.1⟩
    · have hside : i₁ ≠ j₁ := fun h => hij (Prod.ext rfl h)
      exact ⟨zero_of_different_signs hside hx.2.2 hy.2.2, hx.2.1⟩
  · exact fun x hx => ⟨axis_subset_arc F i hx, axis_subset_arc F j hx⟩

theorem region_inter_graph (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool × Bool) :
    region F i ∩ graph F = arc F (false, i.2) ∪ arc F (true, i.1) := by
  apply Subset.antisymm
  · rintro x ⟨hx, hy⟩
    rcases hy.2 with hheight | hsurface
    · exact Or.inl ⟨hx.1, hheight, hx.2.2⟩
    · exact Or.inr ⟨hx.1, hsurface, hx.2.1⟩
  · rintro x (hx | hx)
    · exact ⟨⟨hx.1, hx.2.1 ▸ weakSign_zero i.1, hx.2.2⟩,
        hx.1, Or.inl hx.2.1⟩
    · exact ⟨⟨hx.1, hx.2.2, hx.2.1 ▸ weakSign_zero i.2⟩,
        hx.1, Or.inr hx.2.1⟩

theorem region_contacts (F : Set ((ℝ × ℝ) × ℝ)) :
    Pairwise (fun i j => region F i ∩ region F j ⊆
      arc F (false, i.2) ∪ arc F (true, i.1)) := by
  intro i j hij x hx
  by_cases hheight : i.1 = j.1
  · have hsurface : i.2 ≠ j.2 := fun h => hij (Prod.ext hheight h)
    exact Or.inr ⟨hx.1.1,
      zero_of_different_signs hsurface hx.1.2.2 hx.2.2.2, hx.1.2.1⟩
  · exact Or.inl ⟨hx.1.1,
      zero_of_different_signs hheight hx.1.2.1 hx.2.2.1, hx.1.2.2⟩

theorem iUnion_region (F : Set ((ℝ × ℝ) × ℝ)) : (⋃ i, region F i) = F := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact hxi.1
  · intro x hx
    rcases le_total 0 x.1.1 with ht | ht <;> rcases le_total 0 x.2 with hz | hz
    · exact mem_iUnion.mpr ⟨(false, false), hx, ht, hz⟩
    · exact mem_iUnion.mpr ⟨(false, true), hx, ht, hz⟩
    · exact mem_iUnion.mpr ⟨(true, false), hx, ht, hz⟩
    · exact mem_iUnion.mpr ⟨(true, true), hx, ht, hz⟩

theorem iUnion_arc (F : Set ((ℝ × ℝ) × ℝ)) : (⋃ i, arc F i) = graph F := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨⟨i, j⟩, hxi⟩ := mem_iUnion.mp hx
    refine ⟨hxi.1, ?_⟩
    cases i
    · exact Or.inl hxi.2.1
    · exact Or.inr hxi.2.1
  · rintro x ⟨hx, hzero⟩
    rcases hzero with ht | hz
    · rcases le_total 0 x.2 with h | h
      · exact mem_iUnion.mpr ⟨(false, false), hx, ht, h⟩
      · exact mem_iUnion.mpr ⟨(false, true), hx, ht, h⟩
    · rcases le_total 0 x.1.1 with h | h
      · exact mem_iUnion.mpr ⟨(true, false), hx, hz, h⟩
      · exact mem_iUnion.mpr ⟨(true, true), hx, hz, h⟩

theorem arc_kind_union (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool) :
    arc F (i, false) ∪ arc F (i, true) =
      F ∩ {x | if i then x.2 = 0 else x.1.1 = 0} := by
  cases i
  · ext x
    change ((x ∈ F ∧ x.1.1 = 0 ∧ 0 ≤ x.2) ∨ (x ∈ F ∧ x.1.1 = 0 ∧ x.2 ≤ 0)) ↔
      (x ∈ F ∧ x.1.1 = 0)
    constructor
    · exact fun hx => hx.elim (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
    · intro hx
      exact (le_total 0 x.2).elim
        (fun h => Or.inl ⟨hx.1, hx.2, h⟩) (fun h => Or.inr ⟨hx.1, hx.2, h⟩)
  · ext x
    change ((x ∈ F ∧ x.2 = 0 ∧ 0 ≤ x.1.1) ∨ (x ∈ F ∧ x.2 = 0 ∧ x.1.1 ≤ 0)) ↔
      (x ∈ F ∧ x.2 = 0)
    constructor
    · exact fun hx => hx.elim (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
    · intro hx
      exact (le_total 0 x.1.1).elim
        (fun h => Or.inl ⟨hx.1, hx.2, h⟩) (fun h => Or.inr ⟨hx.1, hx.2, h⟩)

theorem region_height_union (F : Set ((ℝ × ℝ) × ℝ)) (i : Bool) :
    region F (i, false) ∪ region F (i, true) = F ∩ {x | weakSign i x.1.1} := by
  ext x
  change ((x ∈ F ∧ weakSign i x.1.1 ∧ 0 ≤ x.2) ∨
    (x ∈ F ∧ weakSign i x.1.1 ∧ x.2 ≤ 0)) ↔ (x ∈ F ∧ weakSign i x.1.1)
  constructor
  · exact fun hx => hx.elim (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  · intro hx
    exact (le_total 0 x.2).elim
      (fun h => Or.inl ⟨hx.1, hx.2, h⟩) (fun h => Or.inr ⟨hx.1, hx.2, h⟩)

theorem region_transverse_union (F : Set ((ℝ × ℝ) × ℝ)) (j : Bool) :
    region F (false, j) ∪ region F (true, j) = F ∩ {x | weakSign j x.2} := by
  ext x
  change ((x ∈ F ∧ 0 ≤ x.1.1 ∧ weakSign j x.2) ∨
    (x ∈ F ∧ x.1.1 ≤ 0 ∧ weakSign j x.2)) ↔ (x ∈ F ∧ weakSign j x.2)
  constructor
  · exact fun hx => hx.elim (fun h => ⟨h.1, h.2.2⟩) (fun h => ⟨h.1, h.2.2⟩)
  · intro hx
    exact (le_total 0 x.1.1).elim
      (fun h => Or.inl ⟨hx.1, h, hx.2⟩) (fun h => Or.inr ⟨hx.1, h, hx.2⟩)

end CoordinateFourRegions
