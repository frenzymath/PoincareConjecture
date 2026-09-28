import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.CentroidMesh
import PoincareConjecture.Proofs.M76.Mathlib.PositiveAffineCenters










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]




def RespectsAffineHyperplane (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ) : Prop :=
  ∀ s ∈ K.faces,
    (∀ x ∈ convexHull ℝ (s : Set E), A x ≤ 0) ∨
      (∀ x ∈ convexHull ℝ (s : Set E), 0 ≤ A x)



theorem IsSubdivision.respectsAffineHyperplane {K L : SimplicialComplex ℝ E}
    (hKL : K.IsSubdivision L) {A : E →ᵃ[ℝ] ℝ} (hA : L.RespectsAffineHyperplane A) :
    K.RespectsAffineHyperplane A := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hKL.face_subset s hs
  exact (hA t ht).imp (fun h x hx => h x (hst hx)) (fun h x hx => h x (hst hx))




theorem exists_subdivision_respectsAffineHyperplane (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (A : E →ᵃ[ℝ] ℝ) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧ L.RespectsAffineHyperplane A := by
  classical
  let : Fintype K.faces := hfinite.fintype
  have hcenters (s : K.faces) : ∃ c : E,
      (∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
        (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c) ∧
      ((∃ z : E, (∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
        (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = z) ∧ A z = 0) →
        A c = 0) := by
    by_cases hz : ∃ z : E, (∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
      (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = z) ∧ A z = 0
    · obtain ⟨z, hw, hAz⟩ := hz
      exact ⟨z, hw, fun _ => hAz⟩
    · have hs := K.nonempty_of_mem_faces s.property
      refine ⟨s.val.centroid ℝ id, ⟨s.val.centroidWeights ℝ, ?_,
        s.val.sum_centroidWeights_eq_one_of_nonempty ℝ hs, ?_⟩, fun h => (hz h).elim⟩
      · intro v _
        simp only [Finset.centroidWeights_apply, inv_pos]
        exact_mod_cast hs.card_pos
      · rw [Finset.centroid_eq_inv_card_smul_sum _ hs]
        simp only [Finset.centroidWeights_apply, Finset.smul_sum, id_eq]
  choose c hc hzero using hcenters
  refine ⟨K.derivedSubdivision c hc, K.derivedSubdivision_finite c hc,
    K.derivedSubdivision_isSubdivision c hc, K.derivedSubdivision_card_le c hc hN, ?_⟩
  intro s hs
  obtain ⟨t, _, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc s).mp hs
  have hpair (i : K.faces) (hi : i ∈ t) (j : K.faces) (hj : j ∈ t) :
      (A (c i) ≤ 0 ∧ A (c j) ≤ 0) ∨ (0 ≤ A (c i) ∧ 0 ≤ A (c j)) := by
    rcases hchain i hi j hj with h | h
    · exact Finset.positive_centers_same_side h A (hc i) (hc j) (hzero j)
    · exact (Finset.positive_centers_same_side h A (hc j) (hc i) (hzero i)).imp
        And.symm And.symm
  by_cases hpos : ∃ i ∈ t, 0 < A (c i)
  · obtain ⟨i, hi, hAi⟩ := hpos
    right
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage A)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    rcases hpair i hi j hj with h | h
    · exact (not_lt_of_ge h.1 hAi).elim
    · exact h.2
  · left
    apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage A)
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
    exact le_of_not_gt (fun h => hpos ⟨j, hj, h⟩)




theorem exists_subdivision_respectsAffineHyperplanes (K : SimplicialComplex ℝ E)
    (hfinite : K.faces.Finite) {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1)
    (H : Finset (E →ᵃ[ℝ] ℝ)) :
    ∃ L : SimplicialComplex ℝ E, L.faces.Finite ∧ L.IsSubdivision K ∧
      (∀ s ∈ L.faces, s.card ≤ N + 1) ∧
      ∀ A ∈ H, L.RespectsAffineHyperplane A := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨K, hfinite, IsSubdivision.refl K, hN, by simp⟩
  | @insert A H _ ih =>
    obtain ⟨L, hL, hLK, hLN, hLH⟩ := ih
    obtain ⟨R, hR, hRL, hRN, hRA⟩ := L.exists_subdivision_respectsAffineHyperplane hL hLN A
    refine ⟨R, hR, hRL.trans hLK, hRN, ?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hRA
    · exact hRL.respectsAffineHyperplane (hLH B hB)

end Geometry.SimplicialComplex
