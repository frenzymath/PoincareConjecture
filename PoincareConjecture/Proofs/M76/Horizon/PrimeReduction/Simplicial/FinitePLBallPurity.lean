import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior
import PoincareConjecture.Proofs.M76.Mathlib.AffineStarPurity










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]



theorem exists_full_coface_of_finitePLBallPair_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {b : Set E} (hball : IsFinitePLBallPair F K.space b)
    {f : E → F} (hf : K.AffineOnFaces f) (hinj : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = Module.finrank ℝ F + 1 := by
  classical
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hK
  have hJs : J.space = f '' K.space := hf.embeddedImage_space hinj
  have hJball : IsFinitePLBallPair F J.space (f '' b) := by
    rw [hJs]
    exact hball.image (hf.finitePiecewiseAffineOn hK) hinj
  have hreg : closure (interior J.space) = J.space :=
    hJball.closure_interior_of_finrank_eq rfl
  have hsJ : s.image f ∈ J.faces :=
    (hf.image_mem_embeddedImage_iff hinj (K.subset_space hs)).mpr hs
  have hsne : (convexHull ℝ (s.image f : Set F)).Nonempty :=
    (Finset.coe_nonempty.mpr (J.nonempty_of_mem_faces hsJ)).convexHull
  obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ _) hsne
  obtain ⟨t, ht, htcard, hxt⟩ := J.exists_full_face_of_mem_closure_interior hJ
    (hreg.symm.subset (J.convexHull_subset_space hsJ (intrinsicInterior_subset hx)))
  have hst := J.subset_of_mem_intrinsicInterior_face hsJ ht hx hxt
  rw [hf.embeddedImage_faces hinj] at ht
  obtain ⟨u, hu, rfl⟩ := ht
  refine ⟨u, hu, ?_, ?_⟩
  · intro v hvs
    obtain ⟨w, hwu, hwv⟩ := Finset.mem_image.mp
      (hst (Finset.mem_image.mpr ⟨v, hvs, rfl⟩))
    exact hinj (K.subset_space hu hwu) (K.subset_space hs hvs) hwv ▸ hwu
  · exact (Finset.card_image_iff.mpr (hinj.mono (K.subset_space hu))).symm.trans htcard

end Geometry.SimplicialComplex
