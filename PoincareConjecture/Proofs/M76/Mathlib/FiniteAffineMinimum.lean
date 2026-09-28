import PoincareConjecture.Proofs.M76.Mathlib.FinitePiecewiseAffine










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




theorem exists_finite_subdivision_min_affine (K : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) {ι : Type*} [Finite ι] [Nonempty ι]
    (A : ι → E →ᵃ[ℝ] ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      ∀ s ∈ L.faces, ∃ i, ∀ x ∈ convexHull ℝ (s : Set E), ∀ j, A i x ≤ A j x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let H : Finset (E →ᵃ[ℝ] ℝ) :=
    Finset.univ.biUnion fun i => Finset.univ.image fun j => A i - A j
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L, hL, hLK, _, hLH⟩ := K.exists_subdivision_respectsAffineHyperplanes hK hN H
  refine ⟨L, hL, hLK, fun s hs => ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_min_image
    (fun i => A i (s.centroid ℝ id)) Finset.univ_nonempty
  refine ⟨i, fun x hx j => ?_⟩
  have hmem : A i - A j ∈ H := Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hside := (hLH _ hmem s hs).imp
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
  have hcent : (A i - A j) (s.centroid ℝ id) ≤ 0 :=
    sub_nonpos.mpr (hi j (Finset.mem_univ j))
  exact sub_nonpos.mp (s.affine_nonpos_on_hull_of_centroid
    (L.nonempty_of_mem_faces hs) (A i - A j) hside hcent x hx)




theorem finitePiecewiseAffineOn_of_affine_minimum [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {ι : Type*} [Finite ι] [Nonempty ι] (A : ι → E →ᵃ[ℝ] ℝ) {f : E → ℝ}
    (hf : ∀ x ∈ K.space, ∃ i, f x = A i x ∧ ∀ j, f x ≤ A j x) :
    FinitePiecewiseAffineOn f K.space := by
  obtain ⟨L, hL, hLK, hmin⟩ := K.exists_finite_subdivision_min_affine hK A
  refine ⟨L, hL, hLK.space_eq, fun s hs => ?_⟩
  obtain ⟨i, hi⟩ := hmin s hs
  refine ⟨⟨A i, (A i).continuous_of_finiteDimensional⟩, fun x hx => ?_⟩
  obtain ⟨j, hj, hall⟩ := hf x (hLK.space_eq ▸ L.convexHull_subset_space hs hx)
  exact le_antisymm (hall i) (hj ▸ hi x hx j)

end Geometry.SimplicialComplex
