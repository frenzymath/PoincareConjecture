import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → G}

theorem AffineOnFaces.image_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (f '' (s : Set E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hav : EqOn f a (s : Set E) := ha.mono (subset_convexHull ℝ _)
  calc
    f '' convexHull ℝ (s : Set E) = a '' convexHull ℝ (s : Set E) := ha.image_eq
    _ = convexHull ℝ (a '' (s : Set E)) := a.toAffineMap.image_convexHull _
    _ = convexHull ℝ (f '' (s : Set E)) := congrArg (convexHull ℝ) hav.image_eq.symm

theorem AffineOnFaces.mapsTo_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) {t : Set F} (hst : f '' (s : Set E) ⊆ t) :
    MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ t) := by
  intro x hx
  apply convexHull_mono hst
  rw [← hf.image_convexHull hs]
  exact mem_image_of_mem f hx

theorem AffineOnFaces.mapsTo_space (hf : K.AffineOnFaces f)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.space L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  exact convexHull_subset_space ht (hf.mapsTo_convexHull hs hst hxs)

theorem AffineOnFaces.comp_of_face_images (hf : K.AffineOnFaces f)
    (hg : L.AffineOnFaces g)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    K.AffineOnFaces (g ∘ f) := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  obtain ⟨a, ha⟩ := hf s hs
  obtain ⟨b, hb⟩ := hg t ht
  refine ⟨b.comp a, fun x hx => ?_⟩
  exact (hb (hf.mapsTo_convexHull hs hst hx)).trans (congrArg b (ha hx))

end Geometry.SimplicialComplex
