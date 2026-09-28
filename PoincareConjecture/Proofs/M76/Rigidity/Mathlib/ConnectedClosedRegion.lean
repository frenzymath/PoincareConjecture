import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

open Set

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

theorem IsClosed.isConnected_of_isConnected_frontier {K : Set X}
    (hK : IsClosed K) (hfront : IsConnected (frontier K)) : IsConnected K := by
  have hside (u v : Set X) (hu : IsClosed u) (hv : IsClosed v)
      (hcover : K ⊆ u ∪ v) (hdis : Disjoint u v) (hfu : frontier K ⊆ u) :
      K ⊆ u ∨ K ⊆ v := by
    have heq : K ∩ v = interior K ∩ uᶜ := by
      ext x
      constructor
      · intro hx
        have hxu : x ∉ u := fun h => disjoint_left.mp hdis h hx.2
        exact ⟨(mem_interior_iff_notMem_frontier hx.1).mpr
          (fun h => hxu (hfu h)), hxu⟩
      · intro hx
        have hxK := interior_subset hx.1
        exact ⟨hxK, (hcover hxK).resolve_left hx.2⟩
    have hclopen : IsClopen (K ∩ v) := ⟨hK.inter hv, by
      rw [heq]
      exact isOpen_interior.inter hu.isOpen_compl⟩
    rcases isClopen_iff.mp hclopen with hempty | hall
    · left
      intro x hx
      rcases hcover hx with hxu | hxv
      · exact hxu
      · have h : x ∈ K ∩ v := ⟨hx, hxv⟩
        rw [hempty] at h
        exact h.elim
    · right
      intro x _
      have h : x ∈ K ∩ v := hall.symm ▸ mem_univ x
      exact h.2
  refine ⟨hfront.nonempty.mono hK.frontier_subset,
    (isPreconnected_iff_subset_of_fully_disjoint_closed hK).mpr ?_⟩
  intro u v hu hv hcover hdis
  have hboundary := (isPreconnected_iff_subset_of_disjoint_closed.mp hfront.isPreconnected)
    u v hu hv (hK.frontier_subset.trans hcover) (by rw [hdis.inter_eq, inter_empty])
  rcases hboundary with hfu | hfv
  · exact hside u v hu hv hcover hdis hfu
  · exact (hside v u hv hu (by simpa only [union_comm] using hcover) hdis.symm hfv).symm
