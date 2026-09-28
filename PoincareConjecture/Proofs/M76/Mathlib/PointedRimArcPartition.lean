import PoincareConjecture.Proofs.M76.Mathlib.FinitePLDomination
import PoincareConjecture.Proofs.M76.Mathlib.PointedRimWidthIntervals












set_option autoImplicit false

open Set Geometry

namespace Set





theorem rim_superlevel_truncated_sublevel_partition {X : Type*}
    {b : Set X} {r u : X → ℝ} {a c : ℝ}
    (hhigh : ∀ x ∈ b, a ≤ r x → c < u x) :
    (b ∩ {x | a ≤ r x}) ∪ ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x}) =
        b ∩ {x | c ≤ u x} ∧
      (b ∩ {x | a ≤ r x}) ∩ ((b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x}) =
        b ∩ {x | r x = a} ∧
      b ∩ {x | u x = c} ⊆ (b ∩ {x | r x ≤ a}) ∩ {x | c ≤ u x} := by
  refine ⟨?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro (hx | hx)
      · exact ⟨hx.1, (hhigh x hx.1 hx.2).le⟩
      · exact ⟨hx.1.1, hx.2⟩
    · intro hx
      rcases le_total a (r x) with h | h
      · exact Or.inl ⟨hx.1, h⟩
      · exact Or.inr ⟨⟨hx.1, h⟩, hx.2⟩
  · ext x
    constructor
    · intro hx
      exact ⟨hx.1.1, le_antisymm hx.2.1.2 hx.1.2⟩
    · intro hx
      exact ⟨⟨hx.1, hx.2.ge⟩, ⟨hx.1, hx.2.le⟩, (hhigh x hx.1 hx.2.ge).le⟩
  · intro x hx
    refine ⟨⟨hx.1, ?_⟩, hx.2.ge⟩
    by_contra h
    have hlt := hhigh x hx.1 (le_of_not_ge h)
    exact (ne_of_lt hlt) hx.2.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]






theorem IsFinitePLBallPair.exists_uniform_pointed_rim_cuts
    {d b : Set E} (hd : IsFinitePLBallPair (ℝ × ℝ) d b)
    {r u : E → ℝ} (hr : FinitePiecewiseAffineOn r d)
    (hu : FinitePiecewiseAffineOn u b) (q : b)
    (hrq : r q = 0) (huq : u q = 0)
    (hpos : ∀ x ∈ b, x ≠ q → 0 < u x) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ t ∈ Ioc 0 ε, ∀ a ∈ Ioo (0 : ℝ) 2,
      (∀ x ∈ b, a ≤ r x → t * a < u x) ∧
        IsFinitePLBallPair ℝ (b ∩ {x | t * a ≤ u x}) (b ∩ {x | u x = t * a}) := by
  have hcopy := hu
  obtain ⟨J, hJ, hJb, _⟩ := hcopy
  have hrb : FinitePiecewiseAffineOn r b := by
    rw [← hJb]
    exact hr.restrict J hJ (hJb.subset.trans hd.1)
  have hn (x : E) (hx : x ∈ b) : 0 ≤ u x := by
    by_cases hxq : x = q
    · rw [hxq, huq]
    · exact (hpos x hx hxq).le
  have hz (x : E) (hx : x ∈ b) (hxu : u x = 0) : r x ≤ 0 := by
    by_cases hxq : x = q
    · rw [hxq, hrq]
    · exact False.elim ((ne_of_gt (hpos x hx hxq)) hxu)
  obtain ⟨δ, hδ, hsep⟩ := hrb.exists_small_mul_lt_of_pos hu hn hz
  obtain ⟨η, hη, hwidth⟩ := hd.exists_small_pointed_rim_width_intervals hu q huq hpos
  let ε := min δ (η / 4)
  have hε : 0 < ε := lt_min hδ (div_pos hη (by norm_num))
  refine ⟨ε, hε, fun t ht a ha => ?_⟩
  have htδ : t ∈ Icc 0 δ := ⟨ht.1.le, ht.2.trans (min_le_left _ _)⟩
  have hcut : t * a ∈ Ioo (0 : ℝ) η := by
    refine ⟨mul_pos ht.1 ha.1, ?_⟩
    have htη : t ≤ η / 4 := ht.2.trans (min_le_right _ _)
    have hta : t * a < t * 2 := mul_lt_mul_of_pos_left ha.2 ht.1
    nlinarith
  refine ⟨fun x hx hxa => ?_, (hwidth (t * a) hcut).2⟩
  have hxq : x ≠ q := by
    intro heq
    rw [heq, hrq] at hxa
    exact (not_le_of_gt ha.1) hxa
  exact (mul_le_mul_of_nonneg_left hxa ht.1.le).trans_lt
    (hsep t htδ x hx (hpos x hx hxq))

end Set
