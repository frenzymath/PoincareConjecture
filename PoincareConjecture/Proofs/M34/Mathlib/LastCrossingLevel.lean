import PoincareConjecture.Proofs.M34.Mathlib.FirstExitLevel









set_option autoImplicit false

open Set



theorem ContinuousOn.exists_last_eq_of_lt
    {A B : Type*} [ConditionallyCompleteLinearOrder A] [DenselyOrdered A]
    [TopologicalSpace A] [OrderTopology A]
    [LinearOrder B] [TopologicalSpace B] [OrderClosedTopology B]
    {f : A → B} {a b : A} (hf : ContinuousOn f (Icc a b))
    (hab : a ≤ b) {c : B} (ha : f a ≤ c) (hb : c < f b) :
    ∃ t ∈ Ico a b, f t = c ∧ ∀ s ∈ Ioc t b, c < f s := by
  have hne : (Icc a b ∩ f ⁻¹' {c}).Nonempty := by
    obtain ⟨t, ht, hft⟩ := intermediate_value_Icc hab hf ⟨ha, hb.le⟩
    exact ⟨t, ht, hft⟩
  have hcompact : IsCompact (Icc a b ∩ f ⁻¹' {c}) :=
    isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
  obtain ⟨t, ht⟩ := hcompact.exists_isGreatest hne
  have htb : t < b := by
    have hne : t ≠ b := by
      intro h
      have he : f b = c := h ▸ ht.1.2
      exact (ne_of_gt hb) he
    exact lt_of_le_of_ne ht.1.1.2 hne
  refine ⟨t, ⟨ht.1.1.1, htb⟩, ht.1.2, ?_⟩
  intro s hs
  by_contra hsc
  obtain ⟨r, hr, hfr⟩ := intermediate_value_Icc hs.2
    (hf.mono (Icc_subset_Icc_left (ht.1.1.1.trans hs.1.le)))
    ⟨le_of_not_gt hsc, hb.le⟩
  have hrt := ht.2 ⟨⟨(ht.1.1.1.trans hs.1.le).trans hr.1, hr.2⟩, hfr⟩
  exact (not_lt_of_ge hrt) (hs.1.trans_le hr.1)
