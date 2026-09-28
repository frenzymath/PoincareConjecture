import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedManifoldConditions
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkCofaceCount










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [DecidableEq E]



theorem closedFaceStar_singleton_eq_closedStar (K : SimplicialComplex 𝕜 E) (p : E) :
    K.closedFaceStar {p} = K.closedStar p := by
  ext t
  change (t ∈ K.faces ∧ {p} ∪ t ∈ K.faces) ↔
    (t ∈ K.faces ∧ insert p t ∈ K.faces)
  rw [Finset.singleton_union]

end Algebraic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [DecidableEq E] [DecidableEq F] {K : SimplicialComplex ℝ E} {f : E → F}



theorem AffineOnFaces.embeddedImage_closedStar_space (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {p : E} (hp : {p} ∈ K.faces) :
    ((hf.embeddedImage hinj).closedStar (f p)).space = f '' (K.closedStar p).space := by
  simpa only [Finset.image_singleton, closedFaceStar_singleton_eq_closedStar] using
    hf.embeddedImage_closedFaceStar_space hinj hp



theorem AffineOnFaces.embeddedImage_link_space (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {p : E} (hp : {p} ∈ K.faces) :
    ((hf.embeddedImage hinj).link (f p)).space = f '' (K.link p).space := by
  simpa only [Finset.image_singleton, faceLink_singleton_eq_link] using
    (hf.embeddedImage_faceLink_carrier_vertices hinj hp).1

omit [DecidableEq E] [DecidableEq F] in




theorem AffineOnFaces.embeddedImage_coface_count (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {n k : ℕ}
    (hcount : ∀ s ∈ K.faces, s.card = n →
      {t : Finset E | t ∈ K.faces ∧ t.card = n + 1 ∧ s ⊆ t}.ncard = k) :
    ∀ s ∈ (hf.embeddedImage hinj).faces, s.card = n →
      {t : Finset F | t ∈ (hf.embeddedImage hinj).faces ∧
        t.card = n + 1 ∧ s ⊆ t}.ncard = k := by
  classical
  intro s hs hsc
  rw [hf.embeddedImage_faces hinj] at hs
  obtain ⟨u, hu, rfl⟩ := hs
  have huimage : (u.image f).card = u.card :=
    Finset.card_image_iff.mpr (hinj.mono (K.subset_space hu))
  have huc : u.card = n := huimage.symm.trans hsc
  have hlink := hf.ncard_embeddedImage_faceLink hinj hu
  rw [(hf.embeddedImage hinj).ncard_faceLink_vertices_eq_cofaces,
    K.ncard_faceLink_vertices_eq_cofaces, hsc, huc] at hlink
  exact hlink.trans (hcount u hu huc)

end Geometry.SimplicialComplex
