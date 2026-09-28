import PoincareConjecture.Proofs.M76.Mathlib.LocallyFiniteHyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineCentroidSign

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_locallyFinite_subdivision_max_affine (K : SimplicialComplex ℝ E)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E)))
    {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    {ι : Type*} [Finite ι] [Nonempty ι] (A : ι → E →ᵃ[ℝ] ℝ) :
    ∃ D : SimplicialComplex ℝ E,
      LocallyFinite (fun s : D.faces => convexHull ℝ (s.val : Set E)) ∧
      D.IsSubdivision K ∧ (∀ s ∈ D.faces, s.card ≤ N + 1) ∧
      ∀ s ∈ D.faces, ∃ i, ∀ x ∈ convexHull ℝ (s : Set E), ∀ j, A j x ≤ A i x := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let H : Finset (E →ᵃ[ℝ] ℝ) :=
    Finset.univ.biUnion fun i : ι => Finset.univ.image fun j : ι => A j - A i
  obtain ⟨D, hD, hDK, hDN, hDH⟩ :=
    K.exists_locallyFinite_subdivision_respectsAffineHyperplanes hK hN H
  refine ⟨D, hD, hDK, hDN, fun s hs => ?_⟩
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image
    (fun i => A i (s.centroid ℝ id)) Finset.univ_nonempty
  refine ⟨i, fun x hx j => ?_⟩
  have hmem : A j - A i ∈ H := Finset.mem_biUnion.mpr
    ⟨i, Finset.mem_univ i, Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩
  have hside := (hDH _ hmem s hs).imp
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
    (fun h v hv => h v (subset_convexHull ℝ _ hv))
  have hcent : (A j - A i) (s.centroid ℝ id) ≤ 0 :=
    sub_nonpos.mpr (hi j (Finset.mem_univ j))
  exact sub_nonpos.mp (s.affine_nonpos_on_hull_of_centroid
    (D.nonempty_of_mem_faces hs) (A j - A i) hside hcent x hx)

end Geometry.SimplicialComplex
