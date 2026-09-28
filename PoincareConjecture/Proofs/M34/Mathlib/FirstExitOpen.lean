import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Connected.Clopen









set_option autoImplicit false

open Set



theorem ContinuousOn.exists_first_exit_open
    {A X : Type*} [ConditionallyCompleteLinearOrder A] [DenselyOrdered A]
    [TopologicalSpace A] [OrderTopology A] [TopologicalSpace X]
    {γ : A → X} {a b : A} {U : Set X}
    (hγ : ContinuousOn γ (Icc a b)) (hab : a ≤ b) (hU : IsOpen U)
    (ha : γ a ∈ U) (hb : γ b ∉ U) :
    ∃ t ∈ Ioc a b, γ t ∈ frontier U ∧ ∀ s ∈ Ico a t, γ s ∈ U := by
  let S := Icc a b ∩ γ ⁻¹' Uᶜ
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
    (hγ.preimage_isClosed_of_isClosed isClosed_Icc hU.isClosed_compl) inter_subset_left
  have hSne : S.Nonempty := ⟨b, ⟨hab, le_rfl⟩, hb⟩
  obtain ⟨t, ht⟩ := hS.exists_isLeast hSne
  have hat : a < t := by
    have hne : a ≠ t := by
      intro h
      exact ht.1.2 (h ▸ ha)
    exact lt_of_le_of_ne ht.1.1.1 hne
  have hbefore : ∀ s ∈ Ico a t, γ s ∈ U := by
    intro s hs
    by_contra hnot
    have hts := ht.2 ⟨⟨hs.1, hs.2.le.trans ht.1.1.2⟩, hnot⟩
    exact (not_lt_of_ge hts) hs.2
  have hcont : ContinuousWithinAt γ (Ico a t) t :=
    (hγ t ht.1.1).mono (fun s hs => ⟨hs.1, hs.2.le.trans ht.1.1.2⟩)
  have htcl : t ∈ closure (Ico a t) := by
    rw [closure_Ico hat.ne]
    exact ⟨hat.le, le_rfl⟩
  have hcl : γ t ∈ closure U :=
    closure_mono (image_subset_iff.mpr hbefore) (hcont.mem_closure_image htcl)
  exact ⟨t, ⟨hat, ht.1.1.2⟩, ⟨hcl, fun h => ht.1.2 (interior_subset h)⟩, hbefore⟩




theorem IsPreconnected.exists_mem_frontier_of_mem_not_mem
    {X : Type*} [TopologicalSpace X] {S Y : Set X}
    (hS : IsPreconnected S) (hY : IsClosed Y)
    {x y : X} (hxS : x ∈ S) (hxY : x ∈ Y) (hyS : y ∈ S) (hyY : y ∉ Y) :
    ∃ z ∈ S, z ∈ frontier Y := by
  by_contra hnot
  have havoid : ∀ z ∈ S, z ∉ frontier Y := by simpa only [not_exists, not_and] using hnot
  have hout : S ⊆ Yᶜ := hS.subset_of_closure_inter_subset hY.isOpen_compl
    ⟨y, hyS, hyY⟩ (by
      intro z hz
      by_contra hzY
      have hf : z ∈ frontier Yᶜ :=
        ⟨hz.1, by simpa only [hY.isOpen_compl.interior_eq] using hzY⟩
      rw [frontier_compl] at hf
      exact havoid z hz.2 hf)
  exact hout hxS hxY
