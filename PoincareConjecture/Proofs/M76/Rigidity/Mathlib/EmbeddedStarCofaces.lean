import PoincareConjecture.Proofs.M76.Mathlib.AffineStarFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem faceLink_ncard_eq_two_of_embedded_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = Module.finrank ℝ F)
    {p : E} (hps : p ∈ s) (f : E → F)
    (hf : (K.closedStar p).AffineOnFaces f)
    (hi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    (K.faceLink s).vertices.ncard = 2 := by
  classical
  let N := K.closedStar p
  have hsN : s ∈ N.faces :=
    ⟨hs, by simpa only [Finset.insert_eq_of_mem hps] using hs⟩
  let J := hf.embeddedImage hi
  have hJ : J.faces.Finite := hf.embeddedImage_finite hi
    (hK.subset (fun _ ht => ht.1))
  have hsJ : s.image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hi (N.subset_space hsN)).mpr hsN
  have hcardJ : (s.image f).card = Module.finrank ℝ F :=
    (Finset.card_image_iff.mpr (hi.mono (N.subset_space hsN))).trans hscard
  have hintJ : f p ∈ interior J.space := by
    rw [hf.embeddedImage_space hi]
    exact hint
  have hlink := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hcardJ
    ⟨f p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [hf.ncard_embeddedImage_faceLink hi hsN] at hlink
  have hNl : N.faceLink s = K.faceLink s := by
    change (K.closedStar p).faceLink s = K.faceLink s
    rw [← K.closedFaceStar_singleton_eq_closedStar]
    exact K.closedFaceStar_faceLink_of_subset (Finset.singleton_subset_iff.mpr hps)
  rwa [hNl] at hlink

theorem exists_paired_facet_of_embedded_star
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {s : Finset E} (hs : s ∈ K.faces) (hscard : s.card = Module.finrank ℝ F)
    {p : E} (hps : p ∈ s) (f : E → F)
    (hf : (K.closedStar p).AffineOnFaces f)
    (hi : InjOn f (K.closedStar p).space)
    (hint : f p ∈ interior (f '' (K.closedStar p).space)) :
    ∃ t ∈ K.faces, ∃ u ∈ K.faces,
      s ⊆ t ∧ s ⊆ u ∧ t.card = Module.finrank ℝ F + 1 ∧
      u.card = Module.finrank ℝ F + 1 ∧ t ≠ u ∧
      ∀ v ∈ K.faces, s ⊆ v → v.card = Module.finrank ℝ F + 1 → v = t ∨ v = u := by
  have hlink := K.faceLink_ncard_eq_two_of_embedded_star hK hs hscard hps f hf hi hint
  have hcount : {v | v ∈ K.faces ∧ v.card = Module.finrank ℝ F + 1 ∧ s ⊆ v}.ncard = 2 := by
    rw [K.ncard_faceLink_vertices_eq_cofaces, hscard] at hlink
    exact hlink
  obtain ⟨t, u, htu, hset⟩ := ncard_eq_two.mp hcount
  have ht : t ∈ K.faces ∧ t.card = Module.finrank ℝ F + 1 ∧ s ⊆ t := by
    change t ∈ {v | v ∈ K.faces ∧ v.card = Module.finrank ℝ F + 1 ∧ s ⊆ v}
    rw [hset]
    exact Or.inl rfl
  have hu : u ∈ K.faces ∧ u.card = Module.finrank ℝ F + 1 ∧ s ⊆ u := by
    change u ∈ {v | v ∈ K.faces ∧ v.card = Module.finrank ℝ F + 1 ∧ s ⊆ v}
    rw [hset]
    exact Or.inr rfl
  refine ⟨t, ht.1, u, hu.1, ht.2.2, hu.2.2, ht.2.1, hu.2.1, htu, ?_⟩
  intro v hv hsv hvc
  have hmem : v ∈ {w | w ∈ K.faces ∧ w.card = Module.finrank ℝ F + 1 ∧ s ⊆ w} :=
    ⟨hv, hvc, hsv⟩
  rwa [hset] at hmem

end Geometry.SimplicialComplex
