import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.DisjointIntervalUniqueness











set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Dehn



theorem connected_component_in_one_exterior
    {E : Type*} [TopologicalSpace E] {S A M C B0 B1 K : Set E}
    (hA : IsClosed A) (hM : IsClosed M) (hC : IsClosed C)
    (hAM : Disjoint A M) (hMC : Disjoint M C) (hAC : Disjoint A C)
    (hcover : ((A ∪ M) ∪ C) ∪ (B0 ∪ B1) = S)
    (hK : IsConnected K) (hKS : K ⊆ S) (hKB : Disjoint K (B0 ∪ B1)) :
    (K ⊆ A ∧ Disjoint K M ∧ Disjoint K C) ∨
      (K ⊆ M ∧ Disjoint K A ∧ Disjoint K C) ∨
      (K ⊆ C ∧ Disjoint K A ∧ Disjoint K M) := by
  have hsub : K ⊆ (A ∪ M) ∪ C := by
    intro x hx
    rcases hcover.symm.subset (hKS hx) with h | h
    · exact h
    · exact (Set.disjoint_left.mp hKB hx h).elim
  have hAMC : Disjoint A (M ∪ C) := disjoint_union_right.mpr ⟨hAM, hAC⟩
  have hMAC : Disjoint M (A ∪ C) := disjoint_union_right.mpr ⟨hAM.symm, hMC⟩
  have hCAM : Disjoint C (A ∪ M) := disjoint_union_right.mpr ⟨hAC.symm, hMC.symm⟩
  obtain ⟨x, hx⟩ := hK.nonempty
  rcases hsub hx with (hxA | hxM) | hxC
  · have hKA := subset_of_preconnected_closed_union hA (hM.union hC) hAMC
      hK.isPreconnected (by simpa only [union_assoc] using hsub) ⟨x, hx, hxA⟩
    exact Or.inl ⟨hKA, hAM.mono_left hKA, hAC.mono_left hKA⟩
  · have hKM := subset_of_preconnected_closed_union hM (hA.union hC) hMAC
      hK.isPreconnected (by simpa only [union_left_comm, union_assoc] using hsub) ⟨x, hx, hxM⟩
    exact Or.inr (Or.inl ⟨hKM, hAM.symm.mono_left hKM, hMC.mono_left hKM⟩)
  · have hKC := subset_of_preconnected_closed_union hC (hA.union hM) hCAM
      hK.isPreconnected (by simpa only [union_comm C] using hsub) ⟨x, hx, hxC⟩
    exact Or.inr (Or.inr ⟨hKC, hAC.symm.mono_left hKC, hMC.symm.mono_left hKC⟩)



theorem old_component_retained_or_disjoint
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S A M C QA QM QC B0 B1 K : Set E}
    (hA : IsFinitePLBallPair (ℝ × ℝ) A QA)
    (hM : IsFinitePLBallPair (ℝ × ℝ) M QM)
    (hC : IsFinitePLBallPair (ℝ × ℝ) C QC)
    (hAM : Disjoint A M) (hMC : Disjoint M C) (hAC : Disjoint A C)
    (hcover : ((A ∪ M) ∪ C) ∪ (B0 ∪ B1) = S)
    (hK : IsConnected K) (hKS : K ⊆ S) (hKB : Disjoint K (B0 ∪ B1)) :
    (K ⊆ A ∪ C) ∨ Disjoint K (A ∪ C) := by
  rcases connected_component_in_one_exterior hA.isCompact.isClosed hM.isCompact.isClosed
    hC.isCompact.isClosed hAM hMC hAC hcover hK hKS hKB with
    ⟨hKA, _, _⟩ | ⟨_, hKA, hKC⟩ | ⟨hKC, _, _⟩
  · exact Or.inl (hKA.trans subset_union_left)
  · exact Or.inr (disjoint_union_right.mpr ⟨hKA, hKC⟩)
  · exact Or.inl (hKC.trans subset_union_right)

end PoincareConjecture.M76.Dehn
