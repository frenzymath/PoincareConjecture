import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

set_option autoImplicit false

open Set

universe u

variable {X : Type u} [TopologicalSpace X]

theorem IsPreconnected.exists_mem_frontier_of_mem_of_notMem
    {A C : Set X} (hA : IsPreconnected A) {x y : X}
    (hx : x ∈ A) (hxC : x ∈ C) (hy : y ∈ A) (hyC : y ∉ C) :
    ∃ z ∈ A, z ∈ frontier C := by
  by_contra hnone
  push Not at hnone
  have hsubset : A ⊆ interior C ∪ interior Cᶜ := by
    intro z hz
    have hh : z ∈ (frontier C)ᶜ := hnone z hz
    simpa only [compl_frontier_eq_union_interior] using hh
  have hdisj : Disjoint (interior C) (interior Cᶜ) := by
    apply disjoint_left.mpr
    intro z hz hz'
    exact (interior_subset hz') (interior_subset hz)
  rcases hA.subset_or_subset isOpen_interior isOpen_interior hdisj hsubset with h | h
  · exact hyC (interior_subset (h hy))
  · exact (interior_subset (h hx)) hxC

theorem ContinuousOn.exists_frontier_crossing_before
    {C : Set X} (hC : IsClosed C) {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (ha : γ a ∈ C) (hb : γ b ∉ C) :
    ∃ t ∈ Ico a b, γ t ∈ frontier C := by
  obtain ⟨z, ⟨t, ht, rfl⟩, hf⟩ :=
    (isPreconnected_Icc.image γ hγ).exists_mem_frontier_of_mem_of_notMem
      ⟨a, left_mem_Icc.mpr hab, rfl⟩ ha ⟨b, right_mem_Icc.mpr hab, rfl⟩ hb
  have htb : t < b := lt_of_le_of_ne ht.2 (by
    intro he
    subst t
    exact hb (hC.frontier_subset hf))
  exact ⟨t, ⟨ht.1, htb⟩, hf⟩

theorem ContinuousOn.exists_frontier_crossing_after
    {C : Set X} (hC : IsClosed C) {γ : ℝ → X} {a b : ℝ}
    (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b)
    (ha : γ a ∉ C) (hb : γ b ∈ C) :
    ∃ t ∈ Ioc a b, γ t ∈ frontier C := by
  obtain ⟨z, ⟨t, ht, rfl⟩, hf⟩ :=
    (isPreconnected_Icc.image γ hγ).exists_mem_frontier_of_mem_of_notMem
      ⟨b, right_mem_Icc.mpr hab, rfl⟩ hb ⟨a, left_mem_Icc.mpr hab, rfl⟩ ha
  have hat : a < t := lt_of_le_of_ne ht.1 (by
    intro he
    subst t
    exact ha (hC.frontier_subset hf))
  exact ⟨t, ⟨hat, ht.2⟩, hf⟩

theorem ContinuousOn.exists_first_frontier_before_endpoint
    {V : Set X} (hV : IsOpen V) {γ : ℝ → X} {a b : ℝ}
    (hab : a < b) (hγ : ContinuousOn γ (Icc a b))
    (ha : γ a ∈ V) (hb : γ b ∉ closure V) :
    ∃ c ∈ Ioo a b, γ c ∈ frontier V ∧ MapsTo γ (Ico a c) V := by
  let K : Set ℝ := Icc a b ∩ γ ⁻¹' Vᶜ
  have hK : IsCompact K := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl) inter_subset_left
  have hbK : b ∈ K :=
    ⟨right_mem_Icc.mpr hab.le, fun h => hb (subset_closure h)⟩
  obtain ⟨c, hc, hleast⟩ := hK.exists_isLeast ⟨b, hbK⟩
  have hac : a < c := by
    apply lt_of_le_of_ne hc.1.1
    rintro rfl
    exact hc.2 ha
  have hprefix : MapsTo γ (Ico a c) V := by
    intro s hs
    by_contra hout
    have hcs : c ≤ s := hleast ⟨⟨hs.1, hs.2.le.trans hc.1.2⟩, hout⟩
    exact (not_lt_of_ge hcs) hs.2
  have hclosed : MapsTo γ (Icc a c) (closure V) := by
    have hcont : ContinuousOn γ (closure (Ico a c)) := by
      rw [closure_Ico hac.ne]
      exact hγ.mono (Icc_subset_Icc le_rfl hc.1.2)
    simpa only [closure_Ico hac.ne] using hprefix.closure_of_continuousOn hcont
  have hfront : γ c ∈ frontier V := by
    rw [frontier, hV.interior_eq]
    exact ⟨hclosed (right_mem_Icc.mpr hac.le), hc.2⟩
  have hcb : c < b := by
    by_contra h
    have heq : c = b := le_antisymm hc.1.2 (le_of_not_gt h)
    apply hb
    simpa only [heq] using hclosed (right_mem_Icc.mpr hac.le)
  exact ⟨c, ⟨hac, hcb⟩, hfront, hprefix⟩
