import PoincareConjecture.Proofs.M76.Mathlib.InteriorFullCofaces
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageIncidence











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]





theorem exists_full_coface_of_faceAffine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V → E,
      (K.closedFaceStar {p}).AffineOnFaces a ∧
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = Module.finrank ℝ E + 1 := by
  classical
  intro s hs
  obtain ⟨p, hps⟩ := K.nonempty_of_mem_faces hs
  have hp : {p} ∈ K.faces :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  obtain ⟨a, hf, hinj, hint⟩ := hstars p hp
  let S := K.closedFaceStar {p}
  have hS : S.faces.Finite := finite_closedFaceStar_faces hK {p}
  have hsS : s ∈ S.faces := ⟨hs, by simpa [Finset.singleton_union, hps] using hs⟩
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hS
  have hsJ : s.image a ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (S.subset_space hsS)).mpr hsS
  have hintJ : a p ∈ interior J.space := by
    rw [hf.embeddedImage_space hinj]
    exact hint
  obtain ⟨t, ht, hst, htcard⟩ := J.exists_full_coface_of_hull_meets_interior hJ hsJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu.1, ?_, ?_⟩
  · intro v hvs
    obtain ⟨w, hwu, hwv⟩ := Finset.mem_image.mp
      (hst (Finset.mem_image.mpr ⟨v, hvs, rfl⟩))
    have hwveq := hinj (S.subset_space hu hwu) (S.subset_space hsS hvs) hwv
    exact hwveq ▸ hwu
  · exact (Finset.card_image_iff.mpr (hinj.mono (S.subset_space hu))).symm.trans htcard




theorem exists_full_coface_of_affine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V →ᴬ[ℝ] E,
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = Module.finrank ℝ E + 1 := by
  apply K.exists_full_coface_of_faceAffine_vertex_stars hK
  intro p hp
  obtain ⟨a, hinj, hint⟩ := hstars p hp
  exact ⟨a, (K.closedFaceStar {p}).affineOnFaces_affine a, hinj, hint⟩

end Geometry.SimplicialComplex
