import PoincareConjecture.Proofs.M76.Mathlib.InteriorFacetLinks
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

section Incidence

variable {𝕜 V : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup V] [Module 𝕜 V] [DecidableEq V]




theorem closedFaceStar_faceLink_of_subset (K : SimplicialComplex 𝕜 V)
    {r s : Finset V} (hrs : r ⊆ s) :
    (K.closedFaceStar r).faceLink s = K.faceLink s := by
  ext t
  constructor
  · intro ht
    exact ⟨ht.1.1, ht.2.1, ht.2.2.1⟩
  · intro ht
    refine ⟨⟨ht.1, ?_⟩, ht.2.1, ht.2.2, ?_⟩
    · exact K.down_closed ht.2.2
        (Finset.union_subset_union hrs (Finset.Subset.refl t))
        (Finset.union_nonempty.mpr (Or.inr (K.nonempty_of_mem_faces ht.1)))
    · simpa only [← Finset.union_assoc, Finset.union_eq_right.mpr hrs] using ht.2.2

end Incidence

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [DecidableEq V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]





theorem faceLink_ncard_eq_two_of_faceAffine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V → E,
      (K.closedFaceStar {p}).AffineOnFaces a ∧
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, s.card = Module.finrank ℝ E → (K.faceLink s).vertices.ncard = 2 := by
  classical
  intro s hs hscard
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
  have hcardJ : (s.image a).card = Module.finrank ℝ E :=
    (Finset.card_image_iff.mpr (hinj.mono (S.subset_space hsS))).trans hscard
  have hlink := J.faceLink_ncard_eq_two_of_hull_meets_interior hJ hsJ hcardJ
    ⟨a p, subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨p, hps, rfl⟩), hintJ⟩
  rw [hf.ncard_embeddedImage_faceLink hinj hsS] at hlink
  exact (K.closedFaceStar_faceLink_of_subset
    (Finset.singleton_subset_iff.mpr hps)) ▸ hlink



theorem faceLink_ncard_eq_two_of_affine_vertex_stars
    (K : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hstars : ∀ p : V, {p} ∈ K.faces → ∃ a : V →ᴬ[ℝ] E,
      InjOn a (K.closedFaceStar {p}).space ∧
      a p ∈ interior (a '' (K.closedFaceStar {p}).space)) :
    ∀ s ∈ K.faces, s.card = Module.finrank ℝ E → (K.faceLink s).vertices.ncard = 2 := by
  apply K.faceLink_ncard_eq_two_of_faceAffine_vertex_stars hK
  intro p hp
  obtain ⟨a, hinj, hint⟩ := hstars p hp
  exact ⟨a, (K.closedFaceStar {p}).affineOnFaces_affine a, hinj, hint⟩

end Geometry.SimplicialComplex
