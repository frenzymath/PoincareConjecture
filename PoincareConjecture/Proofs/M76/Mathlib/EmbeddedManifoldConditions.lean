import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

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

theorem AffineOnFaces.isConnected_embeddedImage_faceLink (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hfinite : K.faces.Finite) {s : Finset E} (hs : s ∈ K.faces)
    (hconn : IsConnected (K.faceLink s).space) :
    IsConnected ((hf.embeddedImage hinj).faceLink (s.image f)).space := by
  rw [(hf.embeddedImage_faceLink_carrier_vertices hinj hs).1]
  have hflink : (K.faceLink s).AffineOnFaces f := fun t ht => hf t ht.1
  exact hconn.image f (hflink.continuousOn (finite_faceLink_faces hfinite s))

theorem AffineOnFaces.ncard_embeddedImage_faceLink (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).faceLink (s.image f)).vertices.ncard =
      (K.faceLink s).vertices.ncard := by
  rw [(hf.embeddedImage_faceLink_carrier_vertices hinj hs).2]
  exact (hinj.mono ((K.faceLink_vertices_subset s).trans
    (sdiff_subset.trans K.vertices_subset_space))).ncard_image

end Geometry.SimplicialComplex
