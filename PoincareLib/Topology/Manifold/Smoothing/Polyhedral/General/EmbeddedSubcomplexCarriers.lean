import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedImageIncidence

/-!
# Star and link carriers under embedded images

Exact face correspondence identifies the geometric carrier and
vertex images of every source subcomplex, in particular stars
and links. See Cairns 1940, pp. 798--800 and M76 derivation 79.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Inclusion of face collections gives inclusion of geometric
carriers. See Cairns pp. 798--800 and M76 derivation 79. -/
theorem space_subset_of_le {K L : SimplicialComplex ℝ E} (hKL : K ≤ L) :
    K.space ⊆ L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  exact L.convexHull_subset_space (hKL hs) hxs

variable [FiniteDimensional ℝ E] [DecidableEq F]
  {K : SimplicialComplex ℝ E} {f : E → F}

/-- Exact image faces identify both the carrier and the vertices
of an embedded subcomplex. See Cairns pp. 798--800 and
M76 derivation 79. -/
theorem AffineOnFaces.image_subcomplex_carrier_vertices (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {K₀ : SimplicialComplex ℝ E} {L₀ : SimplicialComplex ℝ F}
    (hK₀ : K₀ ≤ K)
    (hfaces : L₀.faces = (fun s : Finset E => s.image f) '' K₀.faces) :
    L₀.space = f '' K₀.space ∧ L₀.vertices = f '' K₀.vertices := by
  have hf₀ : K₀.AffineOnFaces f := fun s hs => hf s (hK₀ hs)
  have hinj₀ : InjOn f K₀.space := hinj.mono (space_subset_of_le hK₀)
  have he : L₀ = hf₀.embeddedImage hinj₀ := by
    ext s
    rw [hfaces, hf₀.embeddedImage_faces hinj₀]
  rw [he]
  exact ⟨hf₀.embeddedImage_space hinj₀, hf₀.embeddedImage_vertices hinj₀⟩

variable [DecidableEq E]

/-- The image closed star is exactly the image of the source
closed-star carrier. See Cairns pp. 799--800 and M76 derivation 79. -/
theorem AffineOnFaces.embeddedImage_closedFaceStar_space (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).closedFaceStar (s.image f)).space =
      f '' (K.closedFaceStar s).space :=
  (hf.image_subcomplex_carrier_vertices hinj (K.closedFaceStar_le s)
    (hf.embeddedImage_closedFaceStar_faces hinj hs)).1

/-- Face links have exactly the images of the source carriers
and source vertex sets. See Cairns pp. 799--800 and M76 derivation 79. -/
theorem AffineOnFaces.embeddedImage_faceLink_carrier_vertices (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).faceLink (s.image f)).space = f '' (K.faceLink s).space ∧
      ((hf.embeddedImage hinj).faceLink (s.image f)).vertices = f '' (K.faceLink s).vertices :=
  hf.image_subcomplex_carrier_vertices hinj (fun _ ht => ht.1)
    (hf.embeddedImage_faceLink_faces hinj hs)

end Geometry.SimplicialComplex
