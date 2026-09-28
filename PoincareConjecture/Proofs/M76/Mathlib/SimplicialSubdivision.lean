import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




structure IsSubdivision (K L : SimplicialComplex ℝ E) : Prop where

  space_eq : K.space = L.space

  face_subset : ∀ s ∈ K.faces, ∃ t ∈ L.faces,
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)



theorem IsSubdivision.refl (K : SimplicialComplex ℝ E) : K.IsSubdivision K :=
  ⟨rfl, fun s hs => ⟨s, hs, Subset.rfl⟩⟩



theorem IsSubdivision.trans {K L N : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) (hLN : L.IsSubdivision N) : K.IsSubdivision N := by
  refine ⟨hKL.space_eq.trans hLN.space_eq, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := hKL.face_subset s hs
  obtain ⟨u, hu, htu⟩ := hLN.face_subset t ht
  exact ⟨u, hu, hst.trans htu⟩



theorem IsSubdivision.affineOnFaces {K L : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) {f : E → F} (hf : L.AffineOnFaces f) : K.AffineOnFaces f :=
  hf.of_face_containment hKL.face_subset

end Geometry.SimplicialComplex
