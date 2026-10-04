import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.AffineOnFaces

/-!
# Images and aligned compositions of face-affine maps

A map affine on each face takes that face onto the convex hull of the vertex
images. When the source and target faces align, face-affine maps compose on
the same source complex. These are the elementary PL calculations used in
Hamilton 1976, p. 64, and Cairns 1940, pp. 797--798. See M76 derivation 08.
Existence of a subdivision for unaligned maps is a separate obligation.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {K : SimplicialComplex ℝ E} {L : SimplicialComplex ℝ F}
  {f : E → F} {g : F → G}

/-- The image of a simplex under a face-affine map is the convex hull of its
vertex images. See Cairns pp. 797--798 and M76 derivation 08. -/
theorem AffineOnFaces.image_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) :
    f '' convexHull ℝ (s : Set E) = convexHull ℝ (f '' (s : Set E)) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hav : EqOn f a (s : Set E) := ha.mono (subset_convexHull ℝ _)
  calc
    f '' convexHull ℝ (s : Set E) = a '' convexHull ℝ (s : Set E) := ha.image_eq
    _ = convexHull ℝ (a '' (s : Set E)) := a.toAffineMap.image_convexHull _
    _ = convexHull ℝ (f '' (s : Set E)) := congrArg (convexHull ℝ) hav.image_eq.symm

/-- Containment of vertex images implies containment of the whole simplex
image in the corresponding convex hull. See M76 derivation 08. -/
theorem AffineOnFaces.mapsTo_convexHull (hf : K.AffineOnFaces f)
    {s : Finset E} (hs : s ∈ K.faces) {t : Set F} (hst : f '' (s : Set E) ⊆ t) :
    MapsTo f (convexHull ℝ (s : Set E)) (convexHull ℝ t) := by
  intro x hx
  apply convexHull_mono hst
  rw [← hf.image_convexHull hs]
  exact mem_image_of_mem f hx

/-- A face-affine map sending each set of vertices into a target face maps
the entire source carrier into the target carrier. See M76 derivation 08. -/
theorem AffineOnFaces.mapsTo_space (hf : K.AffineOnFaces f)
    (hfaces : ∀ s ∈ K.faces, ∃ t ∈ L.faces, f '' (s : Set E) ⊆ (t : Set F)) :
    MapsTo f K.space L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, hst⟩ := hfaces s hs
  exact convexHull_subset_space ht (hf.mapsTo_convexHull hs hst hxs)

/-- Face-affine maps compose on the same source faces when each source face
maps into one target face. The alignment premise is explicit; see M76
derivation 08 and the PL maps of Hamilton p. 64. -/
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
