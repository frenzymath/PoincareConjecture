import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcNeighborhoodBoundaryContact
import PoincareConjecture.Proofs.M76.Wall.Mathlib.BinaryNeighborhoodImage











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex





theorem image_arc_feet_binaryLevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K A D : SimplicialComplex ℝ E) [Fintype K.faces] [Fintype D.faces]
    (hAK : A ≤ K) (hDK : D ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    {a b : E} (hab : a ≠ b) (hcontact : A.space ∩ D.space = {a, b})
    {F : E → E} {h : E → ℝ}
    (hF : K.barycentricSubdivision.AffineOnFaces F)
    (hcenters : ∀ s : K.faces, F (s.val.centroid ℝ id) = s.val.binaryFaceCenter A.vertices)
    (hh : K.AffineOnFaces h)
    (hvalues : ∀ v ∈ K.vertices,
      (v ∈ A.vertices → h v = 1) ∧ (v ∉ A.vertices → h v = 0))
    (hinj : InjOn F K.space) (hmark : F '' D.space = D.space) :
    F '' (D.barycentricDualBlock {a}).space ∪
        F '' (D.barycentricDualBlock {b}).space =
      D.space ∩ {x | (1 / 2 : ℝ) ≤ h x} := by
  obtain ⟨hfeet, _⟩ := K.arc_neighborhood_boundary_contact A D hAK hDK hfull hab hcontact
  have hNK : (K.barycentricNeighborhood A).space ⊆ K.space := by
    intro x hx
    exact K.barycentricSubdivision_isSubdivision.space_eq.subset
      (space_subset_of_le (K.barycentricNeighborhood_le A) hx)
  rw [← image_union, ← hfeet, hinj.image_inter hNK (space_subset_of_le hDK),
    K.image_barycentricNeighborhood_binaryCenters A hF hcenters hh hvalues, hmark]
  ext x
  constructor
  · rintro ⟨⟨_, hx⟩, hxD⟩
    exact ⟨hxD, hx⟩
  · rintro ⟨hxD, hx⟩
    exact ⟨⟨space_subset_of_le hDK hxD, hx⟩, hxD⟩

end Geometry.SimplicialComplex
