import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Lattice

set_option autoImplicit false

open Set

namespace Set

theorem pointed_collar_level_source_partition {X : Type*}
    {B b k : Set X} {q : X} {upper g r : X → ℝ} {t a : ℝ}
    (hB : B = b ∪ k) (htouch : b ∩ k ⊆ {q}) (hzero : upper q = 0)
    (hgr : EqOn g r b) (hgk : ∀ x ∈ k, g x = 0)
    (ht : 0 < t) (hc : 0 < t * a) :
    {x : X | x ∈ B ∧ t * a ≤ upper x} =
        (b ∩ {x | t * a ≤ upper x}) ∪ (k ∩ {x | t * a ≤ upper x}) ∧
      {x : X | x ∈ B ∧ t * a ∈ Icc (t * g x) (upper x)} =
        ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}) ∪
          (k ∩ {x | t * a ≤ upper x}) ∧
      Disjoint (b ∩ {x | t * a ≤ upper x}) (k ∩ {x | t * a ≤ upper x}) ∧
      Disjoint ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x})
        (k ∩ {x | t * a ≤ upper x}) := by
  have hdisj : Disjoint (b ∩ {x | t * a ≤ upper x})
      (k ∩ {x | t * a ≤ upper x}) := by
    apply disjoint_left.mpr
    intro x hx hy
    have hxq : x = q := htouch ⟨hx.1, hy.1⟩
    have hle : t * a ≤ 0 := by
      have hxu : t * a ≤ upper x := hx.2
      simpa only [hxq, hzero] using hxu
    exact (not_le_of_gt hc) hle
  have hsub : ((b ∩ {x | r x ≤ a}) ∩ {x | t * a ≤ upper x}) ⊆
      b ∩ {x | t * a ≤ upper x} := fun _ hx => ⟨hx.1.1, hx.2⟩
  refine ⟨?_, ?_, hdisj, hdisj.mono hsub Subset.rfl⟩
  · ext x
    simp only [hB, mem_ofPred_eq, mem_union, mem_inter_iff]
    tauto
  · ext x
    constructor
    · intro hx
      rcases hB.subset hx.1 with hxb | hxk
      · apply Or.inl
        refine ⟨⟨hxb, ?_⟩, hx.2.2⟩
        have hmul : t * r x ≤ t * a := by
          simpa only [hgr hxb] using hx.2.1
        exact le_of_mul_le_mul_left hmul ht
      · exact Or.inr ⟨hxk, hx.2.2⟩
    · rintro (hx | hx)
      · refine ⟨hB.symm.subset (Or.inl hx.1.1), ?_, hx.2⟩
        rw [hgr hx.1.1]
        exact mul_le_mul_of_nonneg_left hx.1.2 ht.le
      · refine ⟨hB.symm.subset (Or.inr hx.1), ?_, hx.2⟩
        rw [hgk x hx.1, mul_zero]
        exact hc.le

end Set
