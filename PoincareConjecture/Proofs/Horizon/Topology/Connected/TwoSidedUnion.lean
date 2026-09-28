import PoincareConjecture.Proofs.Horizon.Topology.Connected.BoundaryIncidence

set_option autoImplicit false
open Set
open scoped Topology

namespace Poincare.Topology

variable {X : Type*} [TopologicalSpace X]

theorem subset_union_of_two_sided_neighborhood
    {A B K W U V : Set X} {p : X}
    (hAclosed : IsClosed A) (hBclosed : IsClosed B)
    (hAregular : closure (interior A) = A) (hBregular : closure (interior B) = B)
    (hdisjoint : Disjoint (interior A) (interior B))
    (hpA : p ∈ A) (hpB : p ∈ B) (hW : W ∈ 𝓝 p)
    (hpartition : W \ K = U ∪ V)
    (hU : IsPreconnected U) (hV : IsPreconnected V)
    (hneU : U.Nonempty) (hneV : V.Nonempty)
    (hdense : W ⊆ closure (U ∪ V))
    (hfrontA : W ∩ frontier A ⊆ K) (hfrontB : W ∩ frontier B ⊆ K) :
    W ⊆ A ∪ B := by
  have hUV : U ∪ V ⊆ W \ K := hpartition.symm.subset
  have hside (C : Set X) (hregular : closure (interior C) = C) (hpC : p ∈ C)
      (hfront : W ∩ frontier C ⊆ K) : U ⊆ interior C ∨ V ⊆ interior C := by
    have hpclosure : p ∈ closure (interior C) := hregular.symm ▸ hpC
    obtain ⟨z, hzW, hzC⟩ := mem_closure_iff.mp hpclosure
      (interior W) isOpen_interior (mem_interior_iff_mem_nhds.mpr hW)
    obtain ⟨q, hqC, hqUV⟩ := mem_closure_iff.mp (hdense (interior_subset hzW))
      (interior C) isOpen_interior hzC
    have havoid : Disjoint (U ∪ V) (frontier C) := by
      apply disjoint_left.mpr
      intro y hy hyfront
      exact (hUV hy).2 (hfront ⟨(hUV hy).1, hyfront⟩)
    rcases hqUV with hqU | hqV
    · exact Or.inl (preconnected_subset_interior_of_disjoint_frontier hU
        (havoid.mono_left subset_union_left) ⟨q, hqU, hqC⟩)
    · exact Or.inr (preconnected_subset_interior_of_disjoint_frontier hV
        (havoid.mono_left subset_union_right) ⟨q, hqV, hqC⟩)
  have hsub : U ∪ V ⊆ A ∪ B := by
    rcases hside A hAregular hpA hfrontA with hUA | hVA <;>
      rcases hside B hBregular hpB hfrontB with hUB | hVB
    · obtain ⟨q, hq⟩ := hneU
      exact False.elim (disjoint_left.mp hdisjoint (hUA hq) (hUB hq))
    · exact union_subset_union (hUA.trans interior_subset) (hVB.trans interior_subset)
    · exact union_subset (hUB.trans (interior_subset.trans subset_union_right))
        (hVA.trans (interior_subset.trans subset_union_left))
    · obtain ⟨q, hq⟩ := hneV
      exact False.elim (disjoint_left.mp hdisjoint (hVA hq) (hVB hq))
  exact hdense.trans (closure_minimal hsub (hAclosed.union hBclosed))

end Poincare.Topology
