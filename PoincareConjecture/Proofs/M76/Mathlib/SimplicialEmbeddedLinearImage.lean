import PoincareConjecture.Proofs.M76.Mathlib.ConvexLinearInjectivity
import Mathlib.Analysis.Convex.SimplicialComplex.Basic

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E}

omit [FiniteDimensional ℝ E] in
private theorem image_convexHull_linear (Q : E →L[ℝ] F) (s : Set E) :
    Q '' convexHull ℝ s = convexHull ℝ (Q '' s) := by
  simpa only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] using
    Q.toLinearMap.toAffineMap.image_convexHull s

theorem affineIndependent_image_face (Q : E →L[ℝ] F) (hinj : InjOn Q K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ ((↑) : ↥(Q '' (s : Set E)) → F) := by
  have hrange : range ((↑) : s → E) = (s : Set E) := Subtype.range_coe
  have h := Q.toLinearMap.affineIndependent_comp_of_injOn_convexHull (K.indep hs)
    (by simpa only [hrange, ContinuousLinearMap.coe_coe] using
      hinj.mono (K.convexHull_subset_space hs))
  have he : range (Q ∘ ((↑) : s → E)) = Q '' (s : Set E) := by
    ext y
    simp
  have h' := h.range
  change AffineIndependent ℝ ((↑) : range (Q ∘ ((↑) : s → E)) → F) at h'
  rw [he] at h'
  exact h'

noncomputable def embeddedLinearImage (K : SimplicialComplex ℝ E)
    (Q : E →L[ℝ] F) (hinj : InjOn Q K.space) : SimplicialComplex ℝ F := by
  classical
  refine { K.toPreAbstractSimplicialComplex.map Q with
    indep := ?_
    inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    change AffineIndependent ℝ ((↑) : ↥((s.image Q : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact K.affineIndependent_image_face Q hinj hs
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ x ⟨hxs, hxt⟩
    simp only [Finset.coe_image] at hxs hxt ⊢
    rw [← image_convexHull_linear] at hxs hxt
    obtain ⟨y, hy, hyx⟩ := hxs
    obtain ⟨z, hz, hzx⟩ := hxt
    have he : y = z := hinj (K.convexHull_subset_space hs hy)
      (K.convexHull_subset_space ht hz) (hyx.trans hzx.symm)
    have hyinter := K.inter_subset_convexHull hs ht ⟨hy, he.symm ▸ hz⟩
    have hximage : x ∈ convexHull ℝ (Q '' ((s : Set E) ∩ t)) := by
      rw [← image_convexHull_linear]
      exact ⟨y, hyinter, hyx⟩
    apply convexHull_mono (s := Q '' ((s : Set E) ∩ t)) ?_ hximage
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨mem_image_of_mem Q hv.1, mem_image_of_mem Q hv.2⟩

theorem embeddedLinearImage_faces [DecidableEq F]
    (Q : E →L[ℝ] F) (hinj : InjOn Q K.space) :
    (K.embeddedLinearImage Q hinj).faces =
      (fun s : Finset E => s.image Q) '' K.faces := by
  classical
  change (fun s : Finset E => @Finset.image E F (Classical.decEq F) Q s) '' K.faces = _
  congr 1
  funext s
  ext y
  simp only [Finset.mem_image]

theorem embeddedLinearImage_space (Q : E →L[ℝ] F) (hinj : InjOn Q K.space) :
    (K.embeddedLinearImage Q hinj).space = Q '' K.space := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    rw [embeddedLinearImage_faces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← image_convexHull_linear] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, K.convexHull_subset_space hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_subset_space (s := s.image Q)
      (show s.image Q ∈ (K.embeddedLinearImage Q hinj).faces from
        (embeddedLinearImage_faces Q hinj) ▸ mem_image_of_mem _ hs)
    rw [Finset.coe_image, ← image_convexHull_linear]
    exact mem_image_of_mem Q hxs

end Geometry.SimplicialComplex
