import PoincareConjecture.Proofs.M76.Mathlib.PolyhedralNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedAffineHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.CommonSimplicialRefinement

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_finite_neighborhood_subset_normed {S U : Set E}
    (hS : IsCompact S) (hU : IsOpen U) (hSU : S ⊆ U) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ S ⊆ interior K.space ∧ K.space ⊆ U := by
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  obtain ⟨J, hJ, hSJ, hJU⟩ := exists_finite_neighborhood_subset
    (hS.image e.symm.continuous) (e.symm.toHomeomorph.isOpen_image.mpr hU)
    (image_mono hSU)
  have hf : J.AffineOnFaces e :=
    J.affineOnFaces_affine e.toContinuousLinearMap.toContinuousAffineMap
  refine ⟨hf.embeddedImage e.injective.injOn, hf.embeddedImage_finite _ hJ, ?_, ?_⟩
  · intro x hx
    rw [hf.embeddedImage_space]
    apply e.toHomeomorph.isOpenMap.image_interior_subset
    exact ⟨e.symm x, hSJ (mem_image_of_mem e.symm hx), e.apply_symm_apply x⟩
  · intro x hx
    rw [hf.embeddedImage_space] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨z, hz, he⟩ := hJU hy
    change e.symm z = y at he
    rwa [← he, e.apply_symm_apply]

theorem exists_finite_refinement_of_space_subset (J K : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hK : K.faces.Finite) (hJK : J.space ⊆ K.space) :
    ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ R.IsSubdivision J ∧
      ∀ s ∈ R.faces, ∃ t ∈ K.faces,
        convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  let : Fintype K.faces := hK.fintype
  let N := hJ.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ J.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hJ.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  have hcover (x : E) (hx : x ∈ J.space) :
      ∃ i : K.faces, x ∈ convexHull ℝ (i.val : Set E) := by
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp (hJK hx)
    exact ⟨⟨s, hs⟩, hxs⟩
  obtain ⟨R, hR, hRJ, _, href⟩ := J.exists_subdivision_refines_finite_cover hJ hN
    ((↑) : K.faces → Finset E) (fun i => K.indep i.property) hcover
  refine ⟨R, hR, hRJ, fun s hs => ?_⟩
  obtain ⟨i, hi⟩ := href s hs
  exact ⟨i.val, i.property, hi⟩

theorem AffineOnFaces.exists_finite_neighborhood {K : SimplicialComplex ℝ E}
    {f : E → F} (hf : K.AffineOnFaces f) (hK : K.faces.Finite)
    {S U : Set E} (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ interior K.space ∩ U) :
    ∃ R : SimplicialComplex ℝ E, R.faces.Finite ∧ S ⊆ interior R.space ∧
      R.space ⊆ interior K.space ∩ U ∧ R.AffineOnFaces f := by
  obtain ⟨J, hJ, hSJ, hJU⟩ :=
    exists_finite_neighborhood_subset_normed hS (isOpen_interior.inter hU) hSU
  obtain ⟨R, hR, hRJ, href⟩ := J.exists_finite_refinement_of_space_subset K hJ hK
    (fun _ hx => interior_subset (hJU hx).1)
  refine ⟨R, hR, ?_, ?_, hf.of_face_containment href⟩
  · rwa [hRJ.space_eq]
  · rwa [hRJ.space_eq]

end Geometry.SimplicialComplex
