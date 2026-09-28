import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.FiniteCollarCuts



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem collar_frontier_eq_assigned_endpoints
    {X κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {R : Set X} (O : κ → Set X) (hR : IsCompact R)
    (hO : ∀ i, IsOpen (O i)) (hOR : ∀ i, closure (O i) ⊆ interior R)
    (hdis : Pairwise fun i j => Disjoint (closure (O i)) (closure (O j)))
    (B : κ × Bool → Set X) (hBsub : ∀ j, B j ⊆ closure (O j.1))
    (hfront : frontier (R \ ⋃ i, O i) = frontier R ∪ ⋃ j, B j) (i : κ) :
    frontier (O i) = B (i,false) ∪ B (i,true) := by
  obtain ⟨hQ,_,hQfront,hinc,_⟩ := finite_collar_cut_geometry hR hO hOR hdis
  apply Subset.antisymm
  · intro x hx
    have hxC := frontier_subset_closure hx
    have hxQ : x ∈ frontier (R \ ⋃ j, O j) :=
      hQfront.symm.subset (Or.inr (mem_iUnion.mpr ⟨i,hx⟩))
    rcases hfront.subset hxQ with hxR | hxB
    · exact False.elim (hxR.2 (hOR i hxC))
    · obtain ⟨⟨j,b⟩,hjb⟩ := mem_iUnion.mp hxB
      have hji : j = i := by
        by_contra hne
        exact disjoint_left.mp (hdis hne) (hBsub (j,b) hjb) hxC
      subst j
      cases b
      · exact Or.inl hjb
      · exact Or.inr hjb
  · intro x hx
    have hex : ∃ b, x ∈ B (i,b) := by
      rcases hx with hx | hx
      · exact ⟨false,hx⟩
      · exact ⟨true,hx⟩
    obtain ⟨b,hb⟩ := hex
    exact (hinc i).subset ⟨hBsub (i,b) hb,hQ.isClosed.frontier_subset
      (hfront.symm.subset (Or.inr (mem_iUnion.mpr ⟨(i,b),hb⟩)))⟩

end PoincareConjecture.M76
