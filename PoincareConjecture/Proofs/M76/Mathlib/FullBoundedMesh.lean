import PoincareConjecture.Proofs.M76.Mathlib.FullNormedComplex
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialSubdivision










set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]



theorem IsSubdivision.diam_le {K L : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) {D : ℝ}
    (hD : ∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) ≤ D) :
    ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hKL.face_subset s hs
  exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans (hD t ht)

variable (E) [FiniteDimensional ℝ E]




theorem exists_full_locallyFinite_boundedMesh :
    ∃ (K : SimplicialComplex ℝ E) (D : ℝ), 0 ≤ D ∧ K.space = univ ∧
      LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E)) ∧
      ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D := by
  classical
  let N := Module.finrank ℝ E
  let e : EuclideanSpace ℝ (Fin N) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp [N])
  obtain ⟨J, hJfaces, hJspace, hJ⟩ := exists_fullEuclideanGrid (N := N) 1 (by norm_num)
  have hJmesh (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ J.faces) :
      diam (convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin N)))) ≤ (N + 1 : ℝ) := by
    rw [hJfaces] at hs
    obtain ⟨hne, z, q, hsub⟩ := hs
    simpa only [mul_one] using
      (PoincareConjecture.Proofs.M02.Topology.ambient_grid_simplex_geometry 1
        (by norm_num) z q s hne hsub).2.2.1
  have hf : J.AffineOnFaces e :=
    J.affineOnFaces_affine e.toContinuousLinearMap.toContinuousAffineMap
  let p := e.toHomeomorph.toOpenPartialHomeomorph
  have hsource : J.space ⊆ p.source := subset_univ _
  have hind (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ J.faces) :
      AffineIndependent ℝ ((↑) : ↥(p '' (s : Set _)) → E) :=
    hf.affineIndependent_image_face e.injective.injOn hs
  have hhull (s : Finset (EuclideanSpace ℝ (Fin N))) (hs : s ∈ J.faces) :
      p '' convexHull ℝ (s : Set _) = convexHull ℝ (p '' (s : Set _)) := hf.image_convexHull hs
  let K := J.hullImage p (p.injOn.mono hsource) hind hhull
  have hKspace : K.space = univ := by
    change (J.hullImage p (p.injOn.mono hsource) hind hhull).space = univ
    rw [hullImage_space, hJspace, image_univ]
    exact e.surjective.range_eq
  refine ⟨K, ‖e.toContinuousLinearMap‖ * (N + 1), by positivity, hKspace, ?_, ?_⟩
  · intro y
    exact J.local_faces_hullImage p hsource hind hhull (fun x _ => hJ x)
      y (hKspace.symm ▸ mem_univ y)
  · intro t ht
    rw [hullImage_faces] at ht
    obtain ⟨s, hs, rfl⟩ := ht
    rw [Finset.coe_image, ← hhull s hs]
    exact (e.toContinuousLinearMap.lipschitz.diam_image_le _
      (s.finite_toSet.isCompact_convexHull ℝ).isBounded).trans
      (mul_le_mul_of_nonneg_left (hJmesh s hs) (norm_nonneg _))

end Geometry.SimplicialComplex
