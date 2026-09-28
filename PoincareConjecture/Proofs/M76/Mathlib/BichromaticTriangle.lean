import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Tauto










set_option autoImplicit false

namespace Finset

variable {V : Type*} [DecidableEq V]



def IsBichromaticPair (c : V → Bool) (e : Finset V) : Prop :=
  ∃ x y, c x ≠ c y ∧ e = {x, y}



theorem IsBichromaticPair.card {c : V → Bool} {e : Finset V}
    (he : IsBichromaticPair c e) : e.card = 2 := by
  obtain ⟨x, y, hxy, rfl⟩ := he
  exact card_pair (fun h => hxy (congrArg c h))



theorem union_eq_triangle {e f t : Finset V} (he : e.card = 2) (hf : f.card = 2)
    (ht : t.card = 3) (het : e ⊆ t) (hft : f ⊆ t) (hne : e ≠ f) : e ∪ f = t := by
  have hfne : ¬f ⊆ e := by
    intro hfe
    exact hne (eq_of_subset_of_card_le hfe (by omega)).symm
  have hes : e ⊂ e ∪ f := ssubset_iff_subset_ne.mpr ⟨subset_union_left, by
    intro heq
    exact hfne (heq.symm ▸ subset_union_right)⟩
  have hcard := card_lt_card hes
  exact eq_of_subset_of_card_le (union_subset het hft) (by omega)

private theorem other_bichromaticPair_in_triple (c : V → Bool) {x y z : V}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hcolor : c x ≠ c y) (hcz : c z = c x) :
    ∃! f : Finset V, IsBichromaticPair c f ∧ f ⊆ {x, y, z} ∧ f ≠ {x, y} := by
  refine ⟨{z, y}, ⟨⟨z, y, by simpa only [hcz] using hcolor, rfl⟩, ?_, ?_⟩, ?_⟩
  · simp [insert_subset_iff]
  · intro heq
    have hz : z ∈ ({x, y} : Finset V) := heq ▸ mem_insert_self z {y}
    simp only [mem_insert, mem_singleton] at hz
    exact hz.elim (Ne.symm hxz) (Ne.symm hyz)
  · rintro f ⟨⟨u, v, huv, rfl⟩, hf, hne⟩
    have hu : u = x ∨ u = y ∨ u = z := by
      simpa only [mem_insert, mem_singleton] using hf (mem_insert_self u {v})
    have hv : v = x ∨ v = y ∨ v = z := by
      simpa only [mem_insert, mem_singleton] using hf (mem_insert_of_mem (mem_singleton_self v))
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
      simp_all only [ne_eq, not_true_eq_false, not_false_eq_true, pair_comm]




theorem IsBichromaticPair.existsUnique_other {c : V → Bool} {e t : Finset V}
    (he : IsBichromaticPair c e) (ht : t.card = 3) (het : e ⊆ t) :
    ∃! f : Finset V, IsBichromaticPair c f ∧ f ⊆ t ∧ f ≠ e := by
  have hdiff : (t \ e).card = 1 := by
    rw [card_sdiff_of_subset het, ht, he.card]
  obtain ⟨z, hz⟩ := card_eq_one.mp hdiff
  have hzt : z ∈ t \ e := hz ▸ mem_singleton_self z
  have hte : t = insert z e := by
    rw [← union_sdiff_of_subset het, hz, union_singleton]
  obtain ⟨x, y, hcolor, rfl⟩ := he
  have hxy : x ≠ y := fun h => hcolor (congrArg c h)
  have hxz : x ≠ z := by
    intro heq
    exact (mem_sdiff.mp hzt).2 (heq ▸ mem_insert_self x {y})
  have hyz : y ≠ z := by
    intro heq
    exact (mem_sdiff.mp hzt).2 (heq ▸ mem_insert_of_mem (mem_singleton_self y))
  have hcolors : c z = c x ∨ c z = c y := by
    cases hx : c x <;> cases hy : c y <;> cases hz : c z <;> simp_all
  rcases hcolors with hzcolor | hzcolor
  · have htxyz : t = {x, y, z} := by
      rw [hte]
      ext v
      simp only [mem_insert, mem_singleton]
      tauto
    simpa only [← htxyz] using
      other_bichromaticPair_in_triple c hxy hxz hyz hcolor hzcolor
  · have htyxz : t = {y, x, z} := by
      rw [hte]
      ext v
      simp only [mem_insert, mem_singleton]
      tauto
    rw [pair_comm x y]
    simpa only [← htyxz] using
      other_bichromaticPair_in_triple c hxy.symm hyz hxz hcolor.symm hzcolor




theorem IsBichromaticPair.eq_or_eq_of_subset_triangle {c : V → Bool} {e f g t : Finset V}
    (he : IsBichromaticPair c e) (hf : IsBichromaticPair c f)
    (hg : IsBichromaticPair c g) (ht : t.card = 3)
    (het : e ⊆ t) (hft : f ⊆ t) (hgt : g ⊆ t) (hne : e ≠ f) : g = e ∨ g = f := by
  by_cases hge : g = e
  · exact Or.inl hge
  · exact Or.inr ((he.existsUnique_other ht het).unique
      ⟨hg, hgt, hge⟩ ⟨hf, hft, hne.symm⟩)

end Finset
