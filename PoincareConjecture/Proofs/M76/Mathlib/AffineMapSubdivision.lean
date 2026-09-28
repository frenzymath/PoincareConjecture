import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SimplexHalfspaces
import PoincareConjecture.Proofs.M76.Mathlib.AffineCentroidSign

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {K : SimplicialComplex ℝ E} {f : E → F}

theorem AffineOnFaces.exists_subdivision_mapsTo_cover (hf : K.AffineOnFaces f)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {ι : Type*} [Finite ι] (T : ι → Finset F)
    (hT : ∀ i, AffineIndependent ℝ ((↑) : T i → F))
    (hcover : ∀ x ∈ K.space, ∃ i, f x ∈ convexHull ℝ (T i : Set F)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ L.faces, ∃ i, MapsTo f (convexHull ℝ (s : Set E))
        (convexHull ℝ (T i : Set F)) := by
  classical
  let : Fintype K.faces := hfinite.fintype
  let : Fintype ι := Fintype.ofFinite ι
  choose a ha using fun s : K.faces => hf s.val s.property
  choose H hH using fun i => (T i).exists_affine_halfspaces_convexHull (hT i)
  let Htotal : Finset (E →ᵃ[ℝ] ℝ) := Finset.univ.biUnion fun s : K.faces =>
    Finset.univ.biUnion fun i : ι => (H i).image (fun A => A.comp (a s).toAffineMap)
  obtain ⟨L, hL, hLK, hLN, hLH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hfinite hN Htotal
  refine ⟨L, hL, hLK, hLN, fun r hr => ?_⟩
  have hrne := L.nonempty_of_mem_faces hr
  have hcr : r.centroid ℝ id ∈ convexHull ℝ (r : Set E) := r.centroid_mem_convexHull hrne
  have hcK : r.centroid ℝ id ∈ K.space :=
    hLK.space_eq ▸ L.convexHull_subset_space hr hcr
  obtain ⟨i, hi⟩ := hcover _ hcK
  obtain ⟨s, hs, hrs⟩ := hLK.face_subset r hr
  let j : K.faces := ⟨s, hs⟩
  refine ⟨i, fun x hx => ?_⟩
  rw [hH i] at hi ⊢
  intro A hA
  have hAtotal : A.comp (a j).toAffineMap ∈ Htotal := Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_univ j, Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨A, hA, rfl⟩⟩⟩
  have hside := (hLH _ hAtotal r hr).imp
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
  have hcent : (A.comp (a j).toAffineMap) (r.centroid ℝ id) ≤ 0 := by
    change A (a j (r.centroid ℝ id)) ≤ 0
    rw [← ha j (hrs hcr)]
    exact hi A hA
  have h := r.affine_nonpos_on_hull_of_centroid hrne _ hside hcent x hx
  change A (a j x) ≤ 0 at h
  rwa [← ha j (hrs hx)] at h

end Geometry.SimplicialComplex
