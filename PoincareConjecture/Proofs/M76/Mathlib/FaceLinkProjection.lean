import PoincareConjecture.Proofs.M76.Mathlib.FaceStarSaturation
import PoincareConjecture.Proofs.M76.Mathlib.VertexAbstractComplex
import PoincareConjecture.Proofs.M76.Mathlib.RadialConeCarriers










set_option autoImplicit false

open Set AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

section Algebraic

variable {𝕜 E : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [DecidableEq E]



def faceLink (K : SimplicialComplex 𝕜 E) (s : Finset E) : SimplicialComplex 𝕜 E where
  faces := {t | t ∈ K.faces ∧ Disjoint s t ∧ s ∪ t ∈ K.faces}
  indep ht := K.indep ht.1
  isRelLowerSet_faces := by
    intro t ht
    refine ⟨K.nonempty_of_mem_faces ht.1, ?_⟩
    intro u hut hu
    exact ⟨K.down_closed ht.1 hut hu, ht.2.1.mono_right hut,
      K.down_closed ht.2.2 (Finset.union_subset_union Subset.rfl hut)
        (Finset.union_nonempty.mpr (Or.inr hu))⟩
  inter_subset_convexHull ht hu := K.inter_subset_convexHull ht.1 hu.1



theorem faceLink_le_closedFaceStar (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    K.faceLink s ≤ K.closedFaceStar s := fun _ ht => ⟨ht.1, ht.2.2⟩



theorem finite_faceLink_faces {K : SimplicialComplex 𝕜 E}
    (hK : K.faces.Finite) (s : Finset E) : (K.faceLink s).faces.Finite :=
  hK.subset (fun _ ht => ht.1)



theorem faceLink_vertices_subset (K : SimplicialComplex 𝕜 E) (s : Finset E) :
    (K.faceLink s).vertices ⊆ K.vertices \ (s : Set E) := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro hxs
  exact Finset.disjoint_left.mp hx.2.1 hxs (Finset.mem_singleton_self x)




theorem sdiff_mem_faceLink_or_empty (K : SimplicialComplex 𝕜 E) (s : Finset E)
    {t : Finset E} (ht : t ∈ (K.closedFaceStar s).faces) :
    t \ s ∈ insert ∅ (K.faceLink s).faces := by
  by_cases he : t \ s = ∅
  · exact Or.inl he
  · exact Or.inr ⟨K.down_closed ht.1 Finset.sdiff_subset
      (Finset.nonempty_iff_ne_empty.mpr he),
      Finset.disjoint_left.mpr (fun _ hx hy => (Finset.mem_sdiff.mp hy).2 hx),
      by simpa only [Finset.union_sdiff_self_eq_union] using ht.2⟩

end Algebraic

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [DecidableEq E]

private theorem image_union_of_zero_on (f : E →ᵃ[ℝ] F) {s : Finset E}
    (hs : s.Nonempty) (hf : ∀ x ∈ s, f x = 0) (t : Finset E) :
    f '' ((s ∪ t : Finset E) : Set E) = insert 0 (f '' (t : Set E)) := by
  rw [Finset.coe_union, image_union]
  have hsimage : f '' (s : Set E) = {0} := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hf x hx
    · obtain ⟨x, hx⟩ := hs
      rintro _ rfl
      exact ⟨x, hx, hf x hx⟩
  rw [hsimage, singleton_union]




theorem affine_image_closedFaceStar (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0) :
    f '' (K.closedFaceStar s).space =
      ⋃ t ∈ insert ∅ (K.faceLink s).faces,
        convexHull ℝ (insert 0 (f '' (t : Set E))) := by
  have hsne := K.nonempty_of_mem_faces hs
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    refine mem_iUnion₂.mpr ⟨t \ s, K.sdiff_mem_faceLink_or_empty s ht, ?_⟩
    have hsub : (t : Set E) ⊆ ((s ∪ (t \ s) : Finset E) : Set E) := by
      rw [Finset.union_sdiff_self_eq_union]
      exact Finset.subset_union_right
    have hximage : f x ∈ f '' convexHull ℝ ((s ∪ (t \ s) : Finset E) : Set E) :=
      mem_image_of_mem f (convexHull_mono hsub hxt)
    rwa [f.image_convexHull, image_union_of_zero_on f hsne hf] at hximage
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    have hst : s ∪ t ∈ (K.closedFaceStar s).faces := by
      rcases ht with rfl | ht
      · change s ∪ ∅ ∈ K.faces ∧ s ∪ (s ∪ ∅) ∈ K.faces
        simpa only [Finset.union_empty, Finset.union_self] using And.intro hs hs
      · exact ⟨ht.2.2, by simpa only [← Finset.union_assoc, Finset.union_self] using ht.2.2⟩
    rw [← image_union_of_zero_on f hsne hf, ← f.image_convexHull] at hyt
    obtain ⟨x, hx, rfl⟩ := hyt
    exact mem_image_of_mem f (convexHull_subset_space hst hx)




theorem affine_image_closedFaceStar_eq_radialCone (K : SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (f : E →ᵃ[ℝ] F)
    (hf : ∀ x ∈ s, f x = 0)
    (hr : (K.faceLink s).vertexAbstractComplex.IsRadialEmbedding
      (fun v : (K.faceLink s).vertices => f v)) :
    f '' (K.closedFaceStar s).space =
      (RadialEmbedding.cone
        (⟨_, hr⟩ : (K.faceLink s).vertexAbstractComplex.RadialEmbedding F)).space := by
  rw [K.affine_image_closedFaceStar hs f hf, AbstractSimplicialComplex.RadialEmbedding.cone_space]
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_iUnion₂.mp hy
    rcases ht with rfl | ht
    · exact mem_iUnion₂.mpr ⟨∅, Or.inl rfl, by simpa only [Finset.coe_empty, image_empty] using hyt⟩
    · rw [(K.faceLink s).faces_eq_vertexAbstractComplex_images] at ht
      obtain ⟨r, hr, htr⟩ := ht
      refine mem_iUnion₂.mpr ⟨r, Or.inr hr, ?_⟩
      simpa only [htr, image_image, Function.comp_def] using hyt
  · intro hy
    obtain ⟨r, hr, hyr⟩ := mem_iUnion₂.mp hy
    let t := r.map (Function.Embedding.subtype (fun x => x ∈ (K.faceLink s).vertices))
    have ht : t ∈ insert ∅ (K.faceLink s).faces := by
      rcases hr with rfl | hr
      · exact Or.inl (Finset.map_empty _)
      · exact Or.inr hr
    refine mem_iUnion₂.mpr ⟨t, ht, ?_⟩
    simpa only [t, Finset.coe_map, Function.Embedding.coe_subtype, image_image,
      Function.comp_def] using hyr

end Geometry.SimplicialComplex
