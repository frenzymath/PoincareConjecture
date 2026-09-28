import PoincareConjecture.Proofs.M76.Mathlib.SimplicialEmbeddedAffineImage
import PoincareConjecture.Proofs.M76.Mathlib.FaceLinkProjection

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [DecidableEq E] [DecidableEq F] {K : SimplicialComplex ℝ E} {f : E → F}

omit [DecidableEq E] in

theorem AffineOnFaces.image_mem_embeddedImage_iff (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : (s : Set E) ⊆ K.space) :
    s.image f ∈ (hf.embeddedImage hinj).faces ↔ s ∈ K.faces := by
  rw [hf.embeddedImage_faces hinj]
  constructor
  · rintro ⟨t, ht, he⟩
    have hset : f '' (t : Set E) = f '' (s : Set E) := by
      simpa only [Finset.coe_image] using congrArg (fun u : Finset F => (u : Set F)) he
    have hts := (hinj.image_eq_image_iff (K.subset_space ht) hs).mp hset
    exact Finset.coe_injective hts ▸ ht
  · exact fun hs => ⟨s, hs, rfl⟩

omit [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E] in
private theorem disjoint_images_iff (hinj : InjOn f K.space) {s t : Finset E}
    (hs : (s : Set E) ⊆ K.space) (ht : (t : Set E) ⊆ K.space) :
    Disjoint (s.image f) (t.image f) ↔ Disjoint s t := by
  constructor
  · intro h
    exact Finset.disjoint_left.mpr fun x hx hy => Finset.disjoint_left.mp h
      (Finset.mem_image.mpr ⟨x, hx, rfl⟩) (Finset.mem_image.mpr ⟨x, hy, rfl⟩)
  · intro h
    apply Finset.disjoint_left.mpr
    intro y hy hz
    obtain ⟨x, hx, hxy⟩ := Finset.mem_image.mp hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hz
    have he := hinj (hs hx) (ht hz) (hxy.trans hzy.symm)
    exact Finset.disjoint_left.mp h hx (he.symm ▸ hz)

theorem AffineOnFaces.embeddedImage_closedFaceStar_faces (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).closedFaceStar (s.image f)).faces =
      (fun t : Finset E => t.image f) '' (K.closedFaceStar s).faces := by
  ext u
  constructor
  · rintro ⟨hu, hsu⟩
    rw [hf.embeddedImage_faces hinj] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    refine ⟨t, ⟨ht, ?_⟩, rfl⟩
    apply (hf.image_mem_embeddedImage_iff hinj
      (show ((s ∪ t : Finset E) : Set E) ⊆ K.space by
        simpa only [Finset.coe_union] using
          union_subset (K.subset_space hs) (K.subset_space ht))).mp
    simpa only [Finset.image_union] using hsu
  · rintro ⟨t, ⟨ht, hst⟩, rfl⟩
    refine ⟨(hf.image_mem_embeddedImage_iff hinj (K.subset_space ht)).mpr ht, ?_⟩
    simpa only [Finset.image_union] using
      (hf.image_mem_embeddedImage_iff hinj (K.subset_space hst)).mpr hst

theorem AffineOnFaces.embeddedImage_faceLink_faces (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    ((hf.embeddedImage hinj).faceLink (s.image f)).faces =
      (fun t : Finset E => t.image f) '' (K.faceLink s).faces := by
  ext u
  constructor
  · rintro ⟨hu, hd, hsu⟩
    rw [hf.embeddedImage_faces hinj] at hu
    obtain ⟨t, ht, rfl⟩ := hu
    refine ⟨t, ⟨ht, (disjoint_images_iff hinj (K.subset_space hs) (K.subset_space ht)).mp hd,
      ?_⟩, rfl⟩
    apply (hf.image_mem_embeddedImage_iff hinj
      (show ((s ∪ t : Finset E) : Set E) ⊆ K.space by
        simpa only [Finset.coe_union] using
          union_subset (K.subset_space hs) (K.subset_space ht))).mp
    simpa only [Finset.image_union] using hsu
  · rintro ⟨t, ⟨ht, hd, hst⟩, rfl⟩
    refine ⟨(hf.image_mem_embeddedImage_iff hinj (K.subset_space ht)).mpr ht,
      (disjoint_images_iff hinj (K.subset_space hs) (K.subset_space ht)).mpr hd, ?_⟩
    simpa only [Finset.image_union] using
      (hf.image_mem_embeddedImage_iff hinj (K.subset_space hst)).mpr hst

end Geometry.SimplicialComplex
