import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact










set_option autoImplicit false

open Set




theorem ContinuousOn.exists_first_eq_of_le
    {α β : Type*} [ConditionallyCompleteLinearOrder α] [DenselyOrdered α]
    [TopologicalSpace α] [OrderTopology α]
    [LinearOrder β] [TopologicalSpace β] [OrderClosedTopology β]
    {f : α → β} {a b : α} (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b) {c : β} (ha : f a ≤ c) (hb : c ≤ f b) :
    ∃ t ∈ Icc a b, f t = c ∧ ∀ s ∈ Ico a t, f s < c := by
  have hne : (Icc a b ∩ f ⁻¹' {c}).Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf ⟨ha, hb⟩
    exact ⟨t, ht, hft⟩
  have hcompact : IsCompact (Icc a b ∩ f ⁻¹' {c}) :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t, ht⟩ := hcompact.exists_isLeast hne
  refine ⟨t, ht.1.1, ht.1.2, ?_⟩
  intro s hs
  by_contra hsc
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hs.1
    (hf.mono (Icc_subset_Icc_right (hs.2.le.trans ht.1.1.2))) ⟨ha, le_of_not_gt hsc⟩
  have htr := ht.2 ⟨⟨hr.1, hr.2.trans (hs.2.le.trans ht.1.1.2)⟩, hfr⟩
  exact (not_lt_of_ge htr) (hr.2.trans_lt hs.2)
