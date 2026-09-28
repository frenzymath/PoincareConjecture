import PoincareConjecture.Proofs.M76.Mathlib.AffineMapSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F} {f : E → F} {g : F → G}

theorem AffineOnFaces.comp_of_hull_images (hf : K.AffineOnFaces f)
    (hg : L.AffineOnFaces g)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces,
      MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ (t : Set F))) :
    K.AffineOnFaces (g ∘ f) := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg t ht
  exact ⟨b.comp a, fun x hx => (hb (hst hx)).trans (congrArg b (ha hx))⟩

theorem AffineOnFaces.exists_subdivision_comp [FiniteDimensional ℝ F]
    (hf : K.AffineOnFaces f) (hg : L.AffineOnFaces g)
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hmap : MapsTo f K.space L.space)
    {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) :
    ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ s ∈ R.faces, s.card ≤ N + 1) ∧ R.AffineOnFaces (g ∘ f) := by
  classical
  let : Fintype L.faces := hL.fintype
  have hcover (x : E) (hx : x ∈ K.space) :
      ∃ i : L.faces, f x ∈ convexHull ℝ (i.val : Set F) := by
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp (hmap hx)
    exact ⟨⟨t, ht⟩, hxt⟩
  obtain ⟨R, hR, hRK, hRN, hfaces⟩ := hf.exists_subdivision_mapsTo_cover hK hN
    ((↑) : L.faces → Finset F) (fun i => L.indep i.property) hcover
  refine ⟨R, hR, hRK, hRN, (hRK.affineOnFaces hf).comp_of_hull_images hg ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := hfaces s hs
  exact ⟨i.val, i.property, hi⟩

end Geometry.SimplicialComplex
