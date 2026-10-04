import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.EmbeddedSubcomplexCarriers

/-!
# Purity and closed-link conditions under geometric embeddings

Facewise embeddings preserve full coface cardinalities, connected
link carriers and link vertex counts. See Cairns 1940,
pp. 798--800 and M76 derivation 79.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

/-- Embedded images preserve a prescribed full-coface cardinality.
See Cairns pp. 798--800 and M76 derivation 79. -/
theorem AffineOnFaces.embeddedImage_pure (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {n : ℕ}
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n) :
    ∀ s ∈ (hf.embeddedImage hinj).faces,
      ∃ t ∈ (hf.embeddedImage hinj).faces, s ⊆ t ∧ t.card = n := by
  classical
  intro s hs
  rw [hf.embeddedImage_faces hinj] at hs
  obtain ⟨u, hu, rfl⟩ := hs
  obtain ⟨t, ht, hut, hcard⟩ := hpure u hu
  refine ⟨t.image f, (hf.image_mem_embeddedImage_iff hinj (K.subset_space ht)).mpr ht,
    Finset.image_subset_image hut, ?_⟩
  exact (Finset.card_image_iff.mpr (hinj.mono (K.subset_space ht))).trans hcard

variable [DecidableEq E] [DecidableEq F]

/-- Connected links remain connected under a finite face-affine
embedding. See Cairns pp. 798--800 and M76 derivation 79. -/
theorem AffineOnFaces.isConnected_embeddedImage_faceLink (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hfinite : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces)
    (hconn : IsConnected (K.faceLink s).space) :
    IsConnected ((hf.embeddedImage hinj).faceLink (s.image f)).space := by
  rw [(hf.embeddedImage_faceLink_carrier_vertices hinj hs).1]
  have hflink : (K.faceLink s).AffineOnFaces f := fun t ht => hf t ht.1
  exact hconn.image f (hflink.continuousOn (finite_faceLink_faces hfinite s))

/-- The actual link vertex count is preserved by an embedded
image. See Cairns pp. 798--800 and M76 derivation 79. -/
theorem AffineOnFaces.ncard_embeddedImage_faceLink (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).faceLink (s.image f)).vertices.ncard =
      (K.faceLink s).vertices.ncard := by
  rw [(hf.embeddedImage_faceLink_carrier_vertices hinj hs).2]
  exact (hinj.mono ((K.faceLink_vertices_subset s).trans
    (sdiff_subset.trans K.vertices_subset_space))).ncard_image

end Geometry.SimplicialComplex
