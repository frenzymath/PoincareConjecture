import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Connected.Clopen











set_option autoImplicit false

open Set Topology




theorem closure_connectedComponentIn_subset_union_compl
    {X : Type*} [TopologicalSpace X] (U : Set X) (x : X) :
    closure (connectedComponentIn U x) ⊆ connectedComponentIn U x ∪ Uᶜ := by
  by_cases hx : x ∈ U
  · intro y hy
    by_cases hyU : y ∈ U
    · left
      rw [connectedComponentIn_eq_image hx] at hy ⊢
      have hsub : (⟨y, hyU⟩ : U) ∈ closure (connectedComponent (⟨x, hx⟩ : U)) := by
        rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
        exact hy
      exact ⟨⟨y, hyU⟩,
        (isClosed_connectedComponent (x := (⟨x, hx⟩ : U))).closure_eq ▸ hsub, rfl⟩
    · exact Or.inr hyU
  · simp only [connectedComponentIn_eq_empty hx, closure_empty, empty_subset]




theorem connectedComponentIn_compl_inter_neighborhood_nonempty
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {S V : Set X} (hS : IsClosed S) (hne : S.Nonempty) (hV : IsOpen V)
    (hSV : S ⊆ V) {x : X} (hx : x ∈ Sᶜ) :
    (connectedComponentIn Sᶜ x ∩ V).Nonempty := by
  by_contra hn
  have hdis : connectedComponentIn Sᶜ x ⊆ Vᶜ := by
    intro y hy hyV
    exact hn ⟨y, hy, hyV⟩
  have hclosure : closure (connectedComponentIn Sᶜ x) ⊆ Vᶜ :=
    closure_minimal hdis hV.isClosed_compl
  have hclosed : IsClosed (connectedComponentIn Sᶜ x) := by
    apply isClosed_of_closure_subset
    intro y hy
    rcases closure_connectedComponentIn_subset_union_compl Sᶜ x hy with h | h
    · exact h
    · exact False.elim (hclosure hy (hSV (by simpa only [compl_compl] using h)))
  have hall : connectedComponentIn Sᶜ x = univ :=
    (show IsClopen (connectedComponentIn Sᶜ x) from
      ⟨hclosed, hS.isOpen_compl.connectedComponentIn⟩).eq_univ
        ⟨x, mem_connectedComponentIn hx⟩
  obtain ⟨s, hs⟩ := hne
  exact connectedComponentIn_subset Sᶜ x (hall.symm ▸ mem_univ s) hs




theorem compl_eq_union_connectedComponentIn_of_two_half_collar
    {X : Type*} [TopologicalSpace X] [ConnectedSpace X] [LocallyConnectedSpace X]
    {S V B₀ B₁ : Set X} (hS : IsClosed S) (hne : S.Nonempty) (hV : IsOpen V)
    (hSV : S ⊆ V) (hpartition : V \ S = B₀ ∪ B₁)
    (hB₀ : IsPreconnected B₀) (hB₁ : IsPreconnected B₁)
    {x₀ x₁ : X} (hx₀ : x₀ ∈ B₀) (hx₁ : x₁ ∈ B₁) :
    Sᶜ = connectedComponentIn Sᶜ x₀ ∪ connectedComponentIn Sᶜ x₁ := by
  have hsub : B₀ ∪ B₁ ⊆ Sᶜ := by
    rw [← hpartition]
    exact sdiff_subset_compl V S
  apply Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, hyV⟩ :=
      connectedComponentIn_compl_inter_neighborhood_nonempty hS hne hV hSV hx
    have hyB : y ∈ B₀ ∪ B₁ :=
      hpartition ▸ ⟨hyV, connectedComponentIn_subset Sᶜ x hy⟩
    rcases hyB with hy₀ | hy₁
    · have heq := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq
        (hB₀.subset_connectedComponentIn hx₀ (subset_union_left.trans hsub) hy₀)).symm
      exact Or.inl (heq ▸ mem_connectedComponentIn hx)
    · have heq := (connectedComponentIn_eq hy).trans (connectedComponentIn_eq
        (hB₁.subset_connectedComponentIn hx₁ (subset_union_right.trans hsub) hy₁)).symm
      exact Or.inr (heq ▸ mem_connectedComponentIn hx)
  · exact union_subset (connectedComponentIn_subset _ _) (connectedComponentIn_subset _ _)




theorem frontier_connectedComponentIn_compl_eq_of_closure_subset
    {X : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
    {S B : Set X} (hS : IsClosed S) {x : X}
    (hB : B ⊆ connectedComponentIn Sᶜ x) (hSB : S ⊆ closure B) :
    frontier (connectedComponentIn Sᶜ x) = S := by
  rw [hS.isOpen_compl.connectedComponentIn.frontier_eq]
  apply Subset.antisymm
  · rintro y ⟨hycl, hy⟩
    have h := (closure_connectedComponentIn_subset_union_compl Sᶜ x hycl).resolve_left hy
    simpa only [compl_compl] using h
  · intro y hy
    exact ⟨closure_mono hB (hSB hy), fun h => connectedComponentIn_subset Sᶜ x h hy⟩
