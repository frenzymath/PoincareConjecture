import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.SimplexHalfspaces
import PoincareConjecture.Proofs.M76.Mathlib.AffineCentroidSign











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]





theorem exists_subdivision_refines_finite_cover (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {ι : Type*} [Finite ι] (T : ι → Finset E)
    (hT : ∀ i, AffineIndependent ℝ ((↑) : T i → E))
    (hcover : ∀ x ∈ K.space, ∃ i, x ∈ convexHull ℝ (T i : Set E)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ L.faces, ∃ i, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (T i : Set E) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose H hH using fun i => (T i).exists_affine_halfspaces_convexHull (hT i)
  let Htotal := Finset.univ.biUnion H
  obtain ⟨L, hL, hLK, hLN, hLH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hfinite hN Htotal
  refine ⟨L, hL, hLK, hLN, fun s hs => ?_⟩
  have hsne := L.nonempty_of_mem_faces hs
  have hcL : s.centroid ℝ id ∈ L.space :=
    L.convexHull_subset_space hs (s.centroid_mem_convexHull hsne)
  have hcK : s.centroid ℝ id ∈ K.space := hLK.space_eq ▸ hcL
  obtain ⟨i, hi⟩ := hcover _ hcK
  refine ⟨i, fun x hx => ?_⟩
  rw [hH i] at hi ⊢
  intro A hA
  have hAtotal : A ∈ Htotal := Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hA⟩
  have hside := (hLH A hAtotal s hs).imp
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
  exact s.affine_nonpos_on_hull_of_centroid hsne A hside (hi A hA) x hx




theorem exists_common_finite_subdivision (K L : SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (hL : L.faces.Finite) (hspace : K.space = L.space) :
    ∃ R : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision K ∧ R.IsSubdivision L := by
  classical
  let : Fintype L.faces := hL.fintype
  let N := hK.toFinset.sup Finset.card
  have hN (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  have hcover (x : E) (hx : x ∈ K.space) :
      ∃ i : L.faces, x ∈ convexHull ℝ (i.val : Set E) := by
    rw [hspace] at hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨⟨s, hs⟩, hxs⟩
  obtain ⟨R, hR, hRK, _, href⟩ := K.exists_subdivision_refines_finite_cover hK hN
    ((↑) : L.faces → Finset E) (fun i => L.indep i.property) hcover
  refine ⟨R, hR, hRK, hRK.space_eq.trans hspace, fun s hs => ?_⟩
  obtain ⟨i, hi⟩ := href s hs
  exact ⟨i.val, i.property, hi⟩

end Geometry.SimplicialComplex
