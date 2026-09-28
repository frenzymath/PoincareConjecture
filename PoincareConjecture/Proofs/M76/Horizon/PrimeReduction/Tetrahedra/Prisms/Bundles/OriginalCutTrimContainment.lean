import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.OriginalCompactCutTrim








set_option autoImplicit false
open Set
namespace PoincareConjecture.M76.PrismBelt

theorem physical_cut_component_subset_of_raw_trim
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {K N : Set E} {R Q S : Set X}
    (g : E → X) (F : X → E) (hF : Continuous F)
    (hFK : MapsTo F R K) (hgF : ∀ x ∈ R, g (F x) = x)
    (hQR : Q ⊆ R) (hQS : Disjoint Q S)
    (p : E) (htrim : connectedComponentIn (K \ g ⁻¹' S) p ∩ F '' Q ⊆ N)
    (x : X) (hx : x ∈ Q) (hxp : F x ∈ connectedComponentIn (K \ g ⁻¹' S) p) :
    connectedComponentIn Q x ⊆ g '' N := by
  have hmap : MapsTo F Q (K \ g ⁻¹' S) := by
    intro y hy
    refine ⟨hFK (hQR hy),?_⟩
    change g (F y) ∉ S
    rw [hgF y (hQR hy)]
    exact fun hs => disjoint_left.mp hQS hy hs
  have hcomponent : MapsTo F (connectedComponentIn Q x)
      (connectedComponentIn (K \ g ⁻¹' S) p) := by
    intro y hy
    have hmem := connectedComponentIn_mono (F x) (image_subset_iff.mpr hmap)
      (hF.continuousOn.mapsTo_connectedComponentIn hx hy)
    exact (connectedComponentIn_eq hxp).symm.subset hmem
  intro y hy
  have hyQ := connectedComponentIn_subset Q x hy
  exact ⟨F y,htrim ⟨hcomponent hy,mem_image_of_mem F hyQ⟩,hgF y (hQR hyQ)⟩

end PoincareConjecture.M76.PrismBelt
