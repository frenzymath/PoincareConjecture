import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.affineIndependent_image_face (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) {s : Finset E} (hs : s ∈ K.faces) :
    AffineIndependent ℝ ((↑) : ↥(f '' (s : Set E)) → F) := by
  obtain ⟨a, ha⟩ := hf s hs
  have hinja : InjOn a.toAffineMap (convexHull ℝ (s : Set E)) := by
    intro x hx y hy hxy
    exact hinj (K.convexHull_subset_space hs hx) (K.convexHull_subset_space hs hy)
      ((ha hx).trans (hxy.trans (ha hy).symm))
  have hrange : range ((↑) : s → E) = (s : Set E) := Subtype.range_coe
  have h := a.toAffineMap.affineIndependent_comp_of_injOn_convexHull
    (p := ((↑) : s → E)) (K.indep hs) (by rwa [hrange])
  have he : a.toAffineMap ∘ ((↑) : s → E) = f ∘ ((↑) : s → E) := by
    funext v
    exact (ha (subset_convexHull ℝ _ v.property)).symm
  rw [he] at h
  have hr : range (f ∘ ((↑) : s → E)) = f '' (s : Set E) := by ext y; simp
  have h' := h.range
  change AffineIndependent ℝ ((↑) : range (f ∘ ((↑) : s → E)) → F) at h'
  rwa [hr] at h'

noncomputable def AffineOnFaces.embeddedImage (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) : SimplicialComplex ℝ F := by
  classical
  refine { K.toPreAbstractSimplicialComplex.map f with
    indep := ?_
    inter_subset_convexHull := ?_ }
  · rintro _ ⟨s, hs, rfl⟩
    change AffineIndependent ℝ ((↑) : ↥((s.image f : Finset F) : Set F) → F)
    rw [Finset.coe_image]
    exact hf.affineIndependent_image_face hinj hs
  · rintro _ _ ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩ y ⟨hys, hyt⟩
    simp only [Finset.coe_image] at hys hyt ⊢
    rw [← hf.image_convexHull hs] at hys
    rw [← hf.image_convexHull ht] at hyt
    obtain ⟨x, hx, hxy⟩ := hys
    obtain ⟨z, hz, hzy⟩ := hyt
    have he : x = z := hinj (K.convexHull_subset_space hs hx)
      (K.convexHull_subset_space ht hz) (hxy.trans hzy.symm)
    have hxi := K.inter_subset_convexHull hs ht ⟨hx, he.symm ▸ hz⟩
    have hsint : s ∩ t ∈ K.faces := K.down_closed hs Finset.inter_subset_left
      (Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, by simpa using hxi⟩))
    have hyi : y ∈ convexHull ℝ (f '' ((s : Set E) ∩ t)) := by
      rw [← Finset.coe_inter, ← hf.image_convexHull hsint]
      exact ⟨x, by simpa using hxi, hxy⟩
    exact convexHull_mono (by
      rintro _ ⟨v, hv, rfl⟩
      exact ⟨mem_image_of_mem f hv.1, mem_image_of_mem f hv.2⟩) hyi

theorem AffineOnFaces.embeddedImage_faces [DecidableEq F] (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) :
    (hf.embeddedImage hinj).faces = (fun s : Finset E => s.image f) '' K.faces := by
  classical
  change (fun s : Finset E => @Finset.image E F (Classical.decEq F) f s) '' K.faces = _
  congr 1
  funext s
  ext y
  simp only [Finset.mem_image]

theorem AffineOnFaces.embeddedImage_space (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) : (hf.embeddedImage hinj).space = f '' K.space := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp hy
    rw [hf.embeddedImage_faces hinj] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← hf.image_convexHull hs] at hyt
    obtain ⟨x, hx, hxy⟩ := hyt
    exact ⟨x, K.convexHull_subset_space hs hx, hxy⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    apply convexHull_subset_space (s := s.image f)
      (show s.image f ∈ (hf.embeddedImage hinj).faces from
        (hf.embeddedImage_faces hinj) ▸ mem_image_of_mem _ hs)
    rw [Finset.coe_image, ← hf.image_convexHull hs]
    exact mem_image_of_mem f hxs

theorem AffineOnFaces.embeddedImage_finite (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) (hK : K.faces.Finite) : (hf.embeddedImage hinj).faces.Finite := by
  classical
  rw [hf.embeddedImage_faces hinj]
  exact hK.image _

theorem AffineOnFaces.embeddedImage_vertices (hf : K.AffineOnFaces f)
    (hinj : InjOn f K.space) : (hf.embeddedImage hinj).vertices = f '' K.vertices := by
  classical
  ext y
  constructor
  · intro hy
    have hface : {y} ∈ (hf.embeddedImage hinj).faces := hy
    rw [hf.embeddedImage_faces hinj] at hface
    obtain ⟨s, hs, he⟩ := hface
    have heSet : f '' (s : Set E) = {y} := by
      simpa only [Finset.coe_image, Finset.coe_singleton] using
        congrArg (fun t : Finset F => (t : Set F)) he
    have hymem : y ∈ f '' (s : Set E) := by rw [heSet]; simp
    obtain ⟨x, hx, hxy⟩ := hymem
    exact ⟨x, K.down_closed hs (Finset.singleton_subset_iff.mpr hx)
      (Finset.singleton_nonempty x), hxy⟩
  · rintro ⟨x, hx, rfl⟩
    change {f x} ∈ (hf.embeddedImage hinj).faces
    rw [hf.embeddedImage_faces hinj]
    exact ⟨{x}, hx, by simp⟩

end Geometry.SimplicialComplex
