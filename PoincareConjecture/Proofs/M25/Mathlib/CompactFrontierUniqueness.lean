import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.MetricSpace.Bounded











set_option autoImplicit false

open Set




theorem IsCompact.eq_of_frontier_eq_of_preconnected_interior_compl
    {X : Type*} [MetricSpace X]
    (hunbounded : ¬ Bornology.IsBounded (univ : Set X))
    {K B : Set X} (hK : IsCompact K) (hB : IsCompact B)
    (hinside : IsPreconnected (interior B))
    (houtside : IsPreconnected Bᶜ)
    (hne : (interior K).Nonempty)
    (hfront : frontier K = frontier B) : K = B := by
  have hdis : Disjoint (interior K) Kᶜ :=
    disjoint_left.mpr fun _ hx hy => hy (interior_subset hx)
  have hcover {T : Set X} (havoid : Disjoint T (frontier K)) :
      T ⊆ interior K ∪ Kᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior K
    · exact Or.inl hxi
    · exact Or.inr fun hxK => disjoint_left.mp havoid hx ⟨subset_closure hxK, hxi⟩
  have havoid : Disjoint Bᶜ (frontier K) := by
    rw [hfront]
    exact disjoint_left.mpr fun _ hx hy => hx (hB.isClosed.frontier_subset hy)
  have hKB : K ⊆ B := by
    rcases houtside.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
        hdis (hcover havoid) with hin | hout
    · exfalso
      apply hunbounded
      apply (hB.isBounded.union hK.isBounded).subset
      intro x _
      by_cases hx : x ∈ B
      · exact Or.inl hx
      · exact Or.inr (interior_subset (hin hx))
    · intro x hx
      by_contra hxB
      exact hout hxB hx
  have havoid' : Disjoint (interior B) (frontier K) := by
    rw [hfront]
    exact disjoint_left.mpr fun _ hx hy => hy.2 hx
  have hBi : interior B ⊆ interior K := by
    rcases hinside.subset_or_subset isOpen_interior hK.isClosed.isOpen_compl
        hdis (hcover havoid') with hin | hout
    · exact hin
    · obtain ⟨x, hx⟩ := hne
      exact False.elim (hout (interior_mono hKB hx) (interior_subset hx))
  apply Subset.antisymm hKB
  intro x hx
  have heq : B = interior B ∪ frontier B := by
    rw [← closure_eq_interior_union_frontier, hB.isClosed.closure_eq]
  rcases heq ▸ hx with hxi | hxf
  · exact interior_subset (hBi hxi)
  · exact hK.isClosed.frontier_subset (hfront.symm ▸ hxf)
