import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.OriginalSurfacePieces









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem closed_piece_eq_connected_parent_of_avoids_frontier
    {X γ : Type*} [TopologicalSpace X] [Finite γ]
    {B S : Set X} (hB : IsClosed B) (hS : IsClosed S) (hconn : IsConnected S)
    (P : γ → Set X) (hP : ∀ c, IsClosed (P c))
    (hdis : Pairwise fun c d => Disjoint (P c) (P d))
    (hcover : S ∩ B ⊆ ⋃ c, P c)
    (c : γ) (hne : (P c).Nonempty) (hcS : P c ⊆ S) (hcB : P c ⊆ B)
    (hfront : Disjoint (P c) (frontier B)) :
    P c = S ∧ S ⊆ interior B := by
  classical
  have hcint : P c ⊆ interior B := by
    intro x hx
    by_contra hn
    exact disjoint_left.mp hfront hx ⟨hB.closure_eq.symm ▸ hcB hx,hn⟩
  let O := (S \ interior B) ∪ ⋃ d : {d : γ // d ≠ c}, P d
  have hO : IsClosed O :=
    (hS.sdiff isOpen_interior).union (isClosed_iUnion_of_finite fun d => hP d)
  have hsep : Disjoint (P c) O := by
    apply disjoint_left.mpr
    intro x hxc hxo
    rcases hxo with hxo | hxo
    · exact hxo.2 (hcint hxc)
    · obtain ⟨d,hxd⟩ := mem_iUnion.mp hxo
      exact disjoint_left.mp (hdis d.property) hxd hxc
  have hSO : S ⊆ P c ∪ O := by
    intro x hx
    by_cases hxi : x ∈ interior B
    · obtain ⟨d,hxd⟩ := mem_iUnion.mp (hcover ⟨hx,interior_subset hxi⟩)
      by_cases hdc : d = c
      · exact Or.inl (hdc ▸ hxd)
      · exact Or.inr (Or.inr (mem_iUnion.mpr ⟨⟨d,hdc⟩,hxd⟩))
    · exact Or.inr (Or.inl ⟨hx,hxi⟩)
  have hSC : S ⊆ P c := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn.isPreconnected
      (P c) O (hP c) hO hSO
      (by rw [disjoint_iff_inter_eq_empty.mp hsep]; exact inter_empty S) with h | h
    · exact h
    · obtain ⟨x,hx⟩ := hne
      exact (disjoint_left.mp hsep hx (h (hcS hx))).elim
  exact ⟨Subset.antisymm hcS hSC,hSC.trans hcint⟩

end PoincareConjecture.M76
