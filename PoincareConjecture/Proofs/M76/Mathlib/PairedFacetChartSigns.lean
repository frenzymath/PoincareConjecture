import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetCentroidSigns
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedImageIncidence

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {K : SimplicialComplex ℝ E} {f : E → F}

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
private theorem image_centroid_eq (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    {s : Finset E} (hs : s ∈ K.faces) :
    letI := Classical.decEq F
    (s.image f).centroid ℝ id = f (s.centroid ℝ id) := by
  classical
  have hverts : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x = y :=
    fun x hx y hy hxy => hi (K.subset_space hs hx) (K.subset_space hs hy) hxy
  have himage : s.centroid ℝ f = (s.image f).centroid ℝ id :=
    s.centroid_eq_of_inj_on_of_image_eq ℝ (s.image f) hverts
      (fun _ _ _ _ h => h) (by simp)
  obtain ⟨A, hA⟩ := hf s hs
  have hsum := s.sum_centroidWeights_eq_one_of_nonempty ℝ (K.nonempty_of_mem_faces hs)
  rw [← himage, hA (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))]
  rw [Finset.centroid_def, Finset.centroid_def]
  change s.affineCombination ℝ f (s.centroidWeights ℝ) =
    A.toAffineMap (s.affineCombination ℝ id (s.centroidWeights ℝ))
  rw [s.map_affineCombination id (s.centroidWeights ℝ) hsum A.toAffineMap]
  apply Finset.affineCombination_congr _ (fun _ _ => rfl)
  intro x hx
  exact hA (subset_convexHull ℝ _ hx)

theorem AffineOnFaces.opposite_centroid_signs
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = Module.finrank ℝ F)
    (htc : t.card = Module.finrank ℝ F + 1)
    (huc : u.card = Module.finrank ℝ F + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (A : F →ᵃ[ℝ] ℝ) (hA : A.linear ≠ 0) (hzero : ∀ x ∈ s, A (f x) = 0) :
    (A (f (t.centroid ℝ id)) < 0 ∧ 0 < A (f (u.centroid ℝ id))) ∨
      (0 < A (f (t.centroid ℝ id)) ∧ A (f (u.centroid ℝ id)) < 0) := by
  classical
  let L := hf.embeddedImage hi
  have hface {v : Finset E} (hv : v ∈ K.faces) : v.image f ∈ L.faces := by
    rw [hf.embeddedImage_faces]
    exact ⟨v, hv, rfl⟩
  have hcard {v : Finset E} (hv : v ∈ K.faces) : (v.image f).card = v.card :=
    Finset.card_image_iff.mpr (hi.mono (K.subset_space hv))
  have htu' : t.image f ≠ u.image f := by
    intro he
    have hsets : f '' (t : Set E) = f '' (u : Set E) := by
      simpa only [Finset.coe_image] using congrArg (fun a : Finset F => (a : Set F)) he
    exact htu (Finset.coe_injective
      ((hi.image_eq_image_iff (K.subset_space ht) (K.subset_space hu)).mp hsets))
  have hsigns := L.opposite_centroid_signs_of_paired_facet (hface hs) (hface ht) (hface hu)
    ((hcard hs).trans hsc) ((hcard ht).trans htc) ((hcard hu).trans huc)
    (Finset.image_subset_image hst) (Finset.image_subset_image hsu) htu' A hA
    (by intro y hy; obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy; exact hzero x hx)
  simpa only [image_centroid_eq hf hi ht, image_centroid_eq hf hi hu] using hsigns

end Geometry.SimplicialComplex
