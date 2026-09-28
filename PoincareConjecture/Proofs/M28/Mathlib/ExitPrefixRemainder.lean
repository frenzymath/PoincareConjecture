import PoincareConjecture.Proofs.M28.Mathlib.FrontierCrossing
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set

theorem ContinuousOn.exists_prefix_in_remainder_of_exit
    {X : Type*} [TopologicalSpace X] {V K F L : Set X}
    (hV : IsOpen V) (hK : IsClosed K) (hKV : K ⊆ V) (hL : IsClosed L)
    (hcover : V ⊆ K ∪ F ∪ L) {gamma : ℝ → X}
    (hgamma : ContinuousOn gamma (Icc (0 : ℝ) 1)) (h0 : gamma 0 ∈ V)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∉ L)
    (hexit : ¬ MapsTo gamma (Icc (0 : ℝ) 1) V) :
    ∃ s ∈ Icc (0 : ℝ) 1, gamma s ∈ F ∧ MapsTo gamma (Icc 0 s) V := by
  let A := Icc (0 : ℝ) 1 ∩ gamma ⁻¹' Vᶜ
  have hA : IsCompact A := isCompact_Icc.of_isClosed_subset
    (hgamma.preimage_isClosed_of_isClosed isClosed_Icc hV.isClosed_compl) inter_subset_left
  have hne : A.Nonempty := by
    by_contra h
    apply hexit
    intro t ht
    by_contra htV
    exact h ⟨t, ht, htV⟩
  obtain ⟨c, hc, hleast⟩ := hA.exists_isLeast hne
  have hcpos : 0 < c := lt_of_le_of_ne hc.1.1 (by
    intro heq
    exact hc.2 (heq ▸ h0))
  have hbefore : MapsTo gamma (Ico (0 : ℝ) c) V := by
    intro t ht
    by_contra htV
    exact (not_lt_of_ge (hleast ⟨⟨ht.1, ht.2.le.trans hc.1.2⟩, htV⟩)) ht.2
  have hsome : ∃ s ∈ Ico (0 : ℝ) c, gamma s ∉ K ∪ L := by
    by_contra hh
    push Not at hh
    have hmaps : MapsTo gamma (Ico (0 : ℝ) c) (K ∪ L) := hh
    have hcont : ContinuousOn gamma (closure (Ico (0 : ℝ) c)) := by
      rw [closure_Ico hcpos.ne]
      exact hgamma.mono (Icc_subset_Icc le_rfl hc.1.2)
    have hclosed : MapsTo gamma (Icc (0 : ℝ) c) (K ∪ L) := by
      simpa only [closure_Ico hcpos.ne, (hK.union hL).closure_eq] using
        hmaps.closure_of_continuousOn hcont
    rcases hclosed (right_mem_Icc.mpr hcpos.le) with hkc | hlc
    · exact hc.2 (hKV hkc)
    · exact havoid c hc.1 hlc
  obtain ⟨s, hs, hout⟩ := hsome
  refine ⟨s, ⟨hs.1, hs.2.le.trans hc.1.2⟩, ?_, ?_⟩
  · rcases hcover (hbefore hs) with (hk | hf) | hl
    · exact False.elim (hout (Or.inl hk))
    · exact hf
    · exact False.elim (hout (Or.inr hl))
  · intro t ht
    exact hbefore ⟨ht.1, ht.2.trans_lt hs.2⟩
