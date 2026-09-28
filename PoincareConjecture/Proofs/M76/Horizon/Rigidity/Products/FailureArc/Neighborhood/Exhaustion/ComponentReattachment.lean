import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

theorem eq_of_all_attachment_faces_in_clopen_piece
    {X : Type*} [TopologicalSpace X] {R A C P : Set X}
    (hR : IsPreconnected R) (hA : IsClosed A) (hC : IsClosed C) (hP : IsClosed P)
    (hPC : P ⊆ C) (hopen : IsOpen ((Subtype.val : C → X) ⁻¹' P))
    (hne : P.Nonempty) (hcover : A ∪ C = R) (hattach : A ∩ C ⊆ P) : C = P := by
  obtain ⟨U,hU,hPU⟩ := Set.exists_open_inter_of_relative_open hPC hopen
  have hdiff : C \ P = C \ U := by
    rw [hPU]
    ext x
    simp only [mem_sdiff,mem_inter_iff]
    tauto
  have hclosed : IsClosed (C \ P) := hdiff ▸ hC.sdiff hU
  have hCR : C ⊆ R := fun _ hx => hcover.subset (Or.inr hx)
  have hcover' : R ⊆ (A ∪ P) ∪ (C \ P) := by
    intro x hx
    rcases hcover.symm.subset hx with ha|hc
    · exact Or.inl (Or.inl ha)
    · by_cases hp : x ∈ P
      · exact Or.inl (Or.inr hp)
      · exact Or.inr ⟨hc,hp⟩
  have hdis : Disjoint (A ∪ P) (C \ P) := by
    apply disjoint_left.mpr
    rintro x (ha|hp) ⟨hc,hnp⟩
    · exact hnp (hattach ⟨ha,hc⟩)
    · exact hnp hp
  apply Subset.antisymm ?_ hPC
  intro x hx
  by_contra hxp
  obtain ⟨p,hp⟩ := hne
  obtain ⟨y,_,hy⟩ := isPreconnected_closed_iff.mp hR (A ∪ P) (C \ P)
    (hA.union hP) hclosed hcover' ⟨p,hCR (hPC hp),Or.inr hp⟩ ⟨x,hCR hx,hx,hxp⟩
  exact disjoint_left.mp hdis hy.1 hy.2

theorem connectedComponent_eq_of_all_attachment_faces
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R A C : Set X}
    (hR : IsPreconnected R) (hA : IsClosed A) (hC : IsCompact C) (he : PLDomain e C)
    {x : X} (hx : x ∈ C) (hcover : A ∪ C = R)
    (hattach : A ∩ C ⊆ connectedComponentIn C x) :
    connectedComponentIn C x = C := by
  let : LocallyPathConnectedSpace C := he.locallyPathConnectedSpace
  exact (eq_of_all_attachment_faces_in_clopen_piece hR hA hC.isClosed
    (Set.isCompact_connectedComponentIn_of_mem hC hx).isClosed
    (connectedComponentIn_subset C x) (Set.isOpen_preimage_connectedComponentIn hx)
    ⟨x,mem_connectedComponentIn hx⟩ hcover hattach).symm

end PoincareConjecture.M76.Dehn.Annuli
