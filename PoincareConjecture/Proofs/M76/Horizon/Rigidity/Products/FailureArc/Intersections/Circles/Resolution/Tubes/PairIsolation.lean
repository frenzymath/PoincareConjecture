import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Resolution.Tubes.LocalConstruction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.CrossingFamily

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

local notation "P2" => (ℝ × ℝ)

theorem exists_isolated_pair_sources
    {X : Type*} {f g : P2 → X} {S T C D : Set P2}
    (hC : IsCompact C) (hD : IsCompact D)
    (hCS : C ⊆ interior S) (hDT : D ⊆ interior T)
    (himage : f '' C = g '' D)
    (hrestS : IsClosed ({x | x ∈ S ∧ f x ∈ g '' T} \ C))
    (hrestT : IsClosed ({y | y ∈ T ∧ g y ∈ f '' S} \ D)) :
    ∃ K L : SimplicialComplex ℝ P2, K.faces.Finite ∧ L.faces.Finite ∧
      K.space ⊆ interior S ∧ L.space ⊆ interior T ∧
      C ⊆ interior K.space ∧ D ⊆ interior L.space ∧
      {x | x ∈ K.space ∧ f x ∈ g '' L.space} = C ∧
      {y | y ∈ L.space ∧ g y ∈ f '' K.space} = D := by
  obtain ⟨K,hK,hCK,hKS⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    hC (isOpen_interior.sdiff hrestS) (fun x hx => ⟨hCS hx,fun h => h.2 hx⟩)
  obtain ⟨L,hL,hDL,hLT⟩ := SimplicialComplex.exists_finite_neighborhood_subset_normed
    hD (isOpen_interior.sdiff hrestT) (fun x hx => ⟨hDT hx,fun h => h.2 hx⟩)
  have hKi : K.space ⊆ interior S := fun _ h => (hKS h).1
  have hLi : L.space ⊆ interior T := fun _ h => (hLT h).1
  refine ⟨K,L,hK,hL,hKi,hLi,hCK,hDL,?_,?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hx,hy⟩
      by_contra hxc
      exact (hKS hx).2 ⟨⟨interior_subset (hKi hx),
        image_mono (hLi.trans interior_subset) hy⟩,hxc⟩
    · intro x hx
      exact ⟨interior_subset (hCK hx), image_mono (hDL.trans interior_subset)
        (himage.subset ⟨x,hx,rfl⟩)⟩
  · apply Subset.antisymm
    · rintro y ⟨hy,hx⟩
      by_contra hyd
      exact (hLT hy).2 ⟨⟨interior_subset (hLi hy),
        image_mono (hKi.trans interior_subset) hx⟩,hyd⟩
    · intro y hy
      exact ⟨interior_subset (hDL hy), image_mono (hCK.trans interior_subset)
        (himage.symm.subset ⟨y,hy,rfl⟩)⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
