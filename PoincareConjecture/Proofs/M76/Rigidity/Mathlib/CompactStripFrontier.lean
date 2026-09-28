import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]

theorem frontier_compact_strip_subset_ends {B : Set E} (hB : IsCompact B)
    {a b : ℝ} {f : E × ℝ → X} (hc : ContinuousOn f (B ×ˢ Icc a b))
    (ho : IsOpen (f '' (B ×ˢ Ioo a b))) :
    frontier (f '' (B ×ˢ Icc a b)) ⊆ f '' (B ×ˢ ({a, b} : Set ℝ)) := by
  have hcompact : IsCompact (f '' (B ×ˢ Icc a b)) :=
    (hB.prod isCompact_Icc).image_of_continuousOn hc
  have hsub : f '' (B ×ˢ Ioo a b) ⊆ f '' (B ×ˢ Icc a b) :=
    image_mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
  intro x hx
  have hximage : x ∈ f '' (B ×ˢ Icc a b) := by
    simpa only [hcompact.isClosed.closure_eq] using frontier_subset_closure hx
  obtain ⟨z, hz, rfl⟩ := hximage
  have hnot : ¬ (a < z.2 ∧ z.2 < b) := by
    intro ht
    exact hx.2 (interior_maximal hsub ho ⟨z, ⟨hz.1, ht⟩, rfl⟩)
  refine ⟨z, ⟨hz.1, ?_⟩, rfl⟩
  by_cases ha : z.2 = a
  · exact Or.inl ha
  · right
    have ha' : a < z.2 := lt_of_le_of_ne hz.2.1 (Ne.symm ha)
    exact le_antisymm hz.2.2 (le_of_not_gt (fun hb => hnot ⟨ha', hb⟩))
