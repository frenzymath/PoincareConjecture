import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Separation.Hausdorff













set_option autoImplicit false

open Set

namespace Poincare.Topology



theorem puncture_mem_interior_of_escaping_sides
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {o : X} {K A B : Set X} (hK : IsCompact K)
    (hinner : (interior K).Nonempty) (hboundary : o ∉ frontier K)
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hcover : A ∪ B = {o}ᶜ \ frontier K)
    (hescape : ∀ L : Set X, IsCompact L → L ⊆ {o}ᶜ →
      ¬ A ⊆ L ∧ ¬ B ⊆ L) : o ∈ interior K := by
  have hsplit : interior K ∪ Kᶜ = (frontier K)ᶜ := by
    rw [compl_frontier_eq_union_interior, hK.isClosed.isOpen_compl.interior_eq]
  have hdis : Disjoint (interior K) Kᶜ :=
    disjoint_left.mpr fun _ hx hx' => hx' (interior_subset hx)
  have hside {V : Set X} (hc : IsPreconnected V) (hV : V ⊆ A ∪ B)
      (hmeet : (V ∩ interior K).Nonempty) : V ⊆ K := by
    apply Subset.trans _ interior_subset
    apply hc.subset_left_of_subset_union isOpen_interior hK.isClosed.isOpen_compl hdis
    · rw [hsplit]
      intro x hx
      exact (hcover ▸ hV hx).2
    · exact hmeet
  have ho : o ∈ K := by
    by_contra ho
    have hKavoid : K ⊆ {o}ᶜ := by
      intro x hx hxo
      exact ho ((mem_singleton_iff.mp hxo) ▸ hx)
    obtain ⟨x, hx⟩ := hinner
    have hxcover : x ∈ A ∪ B := by
      rw [hcover]
      refine ⟨hKavoid (interior_subset hx), ?_⟩
      exact fun h => h.2 hx
    rcases hxcover with hxA | hxB
    · exact (hescape K hK hKavoid).1
        (hside hA subset_union_left ⟨x, hxA, hx⟩)
    · exact (hescape K hK hKavoid).2
        (hside hB subset_union_right ⟨x, hxB, hx⟩)
  by_contra hi
  exact hboundary ⟨subset_closure ho, hi⟩

end Poincare.Topology
