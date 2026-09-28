import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps
import Mathlib.LinearAlgebra.LinearIndependent.Basic











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}

private theorem linear_image_convexHull (Q : E →L[ℝ] F) (s : Set E) :
    Q '' convexHull ℝ s = convexHull ℝ (Q '' s) := by
  simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
    Q.toLinearMap.toAffineMap.image_convexHull s



theorem linearIndependent_linear_face_image (Q : E →L[ℝ] F) {s : Finset E}
    (hlin : LinearIndependent ℝ ((↑) : s → E))
    (hQ : InjOn Q (Submodule.span ℝ (s : Set E))) :
    LinearIndependent ℝ ((↑) : ↥(Q '' (s : Set E)) → F) := by
  have hs : LinearIndepOn ℝ id (s : Set E) := hlin
  have hmap := hs.map_injOn Q.toLinearMap
    (by simpa only [image_id, ContinuousLinearMap.coe_coe] using hQ)
  simpa only [LinearIndepOn, Function.comp_def, id_eq, ContinuousLinearMap.coe_coe]
    using hmap.id_image




noncomputable def linearImage (K : SimplicialComplex ℝ E)
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) : SimplicialComplex ℝ F := by
  classical
  refine { K.toPreAbstractSimplicialComplex.map Q with
    indep := ?_
    inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    have h := linearIndependent_linear_face_image Q (hlin s hs) (hspan s hs)
    change AffineIndependent ℝ ((↑) : ↥((s.image Q : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact h.affineIndependent
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ x ⟨hxs, hxt⟩
    simp only [Finset.coe_image] at hxs hxt ⊢
    rw [← linear_image_convexHull] at hxs hxt
    obtain ⟨y, hy, hyx⟩ := hxs
    obtain ⟨z, hz, hzx⟩ := hxt
    have he : y = z := hinj (convexHull_subset_space hs hy)
      (convexHull_subset_space ht hz) (hyx.trans hzx.symm)
    have hyinter := K.inter_subset_convexHull hs ht ⟨hy, he.symm ▸ hz⟩
    have hximage : x ∈ convexHull ℝ (Q '' ((s : Set E) ∩ t)) := by
      rw [← linear_image_convexHull]
      exact ⟨y, hyinter, hyx⟩
    apply convexHull_mono (s := Q '' ((s : Set E) ∩ t)) ?_ hximage
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu.1, rfl⟩, ⟨u, hu.2, rfl⟩⟩



theorem linearImage_faces [DecidableEq F]
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) :
    (K.linearImage hlin Q hspan hinj).faces =
      (fun s : Finset E => s.image Q) '' K.faces := by
  classical
  change (fun s : Finset E => @Finset.image E F (Classical.decEq F) Q s) '' K.faces = _
  congr 1
  funext s
  ext x
  simp only [Finset.mem_image]



theorem linearIndependent_linearImage_face
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) {t : Finset F} (ht : t ∈ (K.linearImage hlin Q hspan hinj).faces) :
    LinearIndependent ℝ ((↑) : t → F) := by
  classical
  rw [linearImage_faces] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  change LinearIndependent ℝ ((↑) : ↥((s.image Q : Finset F) : Set F) → F)
  rw [Finset.coe_image]
  exact linearIndependent_linear_face_image Q (hlin s hs) (hspan s hs)



theorem linearImage_space
    (hlin : ∀ s ∈ K.faces, LinearIndependent ℝ ((↑) : s → E))
    (Q : E →L[ℝ] F) (hspan : ∀ s ∈ K.faces, InjOn Q (Submodule.span ℝ (s : Set E)))
    (hinj : InjOn Q K.space) :
    (K.linearImage hlin Q hspan hinj).space = Q '' K.space := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    rw [linearImage_faces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← linear_image_convexHull] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, convexHull_subset_space hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_subset_space (s := s.image Q)
      (show s.image Q ∈ (K.linearImage hlin Q hspan hinj).faces from
        (linearImage_faces hlin Q hspan hinj) ▸ mem_image_of_mem _ hs)
    rw [Finset.coe_image, ← linear_image_convexHull]
    exact mem_image_of_mem Q hxs

end Geometry.SimplicialComplex
