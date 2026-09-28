import PoincareConjecture.Proofs.M76.Mathlib.DerivedLocalFiniteness
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision










set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]





theorem exists_locallyFinite_subdivision_respectsAffineHyperplane
    (K : SimplicialComplex ℝ E)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E)))
    {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) (A : E →ᵃ[ℝ] ℝ) :
    ∃ D : SimplicialComplex ℝ E,
      LocallyFinite (fun s : D.faces => convexHull ℝ (s.val : Set E)) ∧
      D.IsSubdivision K ∧ (∀ s ∈ D.faces, s.card ≤ N + 1) ∧
      D.RespectsAffineHyperplane A := by
  classical
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
  choose c₀ hc₀ hz₀ using hcenters
  let c (s : Finset E) : E := if hs : s ∈ K.faces then c₀ ⟨s, hs⟩ else 0
  have hc (s : Finset E) (hs : s ∈ K.faces) :
      ∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
        (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = c s := by
    simpa only [c, dif_pos hs] using hc₀ ⟨s, hs⟩
  have hz (s : Finset E) (hs : s ∈ K.faces) :
      (∃ z : E, (∃ w : E → ℝ, (∀ v ∈ s, 0 < w v) ∧
        (∑ v ∈ s, w v) = 1 ∧ (∑ v ∈ s, w v • v) = z) ∧ A z = 0) → A (c s) = 0 := by
    simpa only [c, dif_pos hs] using hz₀ ⟨s, hs⟩
  obtain ⟨D, hDK, hD⟩ := K.exists_derived_subdivision c hc
  have hcent (s : Finset E) (hs : s ∈ K.faces) : c s ∈ convexHull ℝ (s : Set E) := by
    obtain ⟨w, hw, hsum, hval⟩ := hc s hs
    exact Finset.mem_convexHull'.mpr ⟨w, fun v hv => (hw v hv).le, hsum, hval⟩
  refine ⟨D, locallyFinite_center_chain_faces hcent (fun t ht => (hD t).mp ht) hK,
    hDK, center_chain_faces_card_le (fun t ht => (hD t).mp ht) hN, ?_⟩
  intro t ht
  obtain ⟨a, _, hfaces, hchain, rfl⟩ := (hD t).mp ht
  have hpair (s : Finset E) (hs : s ∈ a) (u : Finset E) (hu : u ∈ a) :
      (A (c s) ≤ 0 ∧ A (c u) ≤ 0) ∨ (0 ≤ A (c s) ∧ 0 ≤ A (c u)) := by
    rcases hchain s hs u hu with h | h
    · exact Finset.positive_centers_same_side h A (hc s (hfaces s hs))
        (hc u (hfaces u hu)) (hz u (hfaces u hu))
    · exact (Finset.positive_centers_same_side h A (hc u (hfaces u hu))
        (hc s (hfaces s hs)) (hz s (hfaces s hs))).imp And.symm And.symm
  by_cases hpos : ∃ s ∈ a, 0 < A (c s)
  · obtain ⟨s, hs, hAs⟩ := hpos
    right
    apply convexHull_min _ ((convex_Ici (0 : ℝ)).affine_preimage A)
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    rcases hpair s hs u hu with h | h
    · exact (not_lt_of_ge h.1 hAs).elim
    · exact h.2
  · left
    apply convexHull_min _ ((convex_Iic (0 : ℝ)).affine_preimage A)
    intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact le_of_not_gt (fun h => hpos ⟨s, hs, h⟩)




theorem exists_locallyFinite_subdivision_respectsAffineHyperplanes
    (K : SimplicialComplex ℝ E)
    (hK : LocallyFinite (fun s : K.faces => convexHull ℝ (s.val : Set E)))
    {N : ℕ} (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) (H : Finset (E →ᵃ[ℝ] ℝ)) :
    ∃ D : SimplicialComplex ℝ E,
      LocallyFinite (fun s : D.faces => convexHull ℝ (s.val : Set E)) ∧
      D.IsSubdivision K ∧ (∀ s ∈ D.faces, s.card ≤ N + 1) ∧
      ∀ A ∈ H, D.RespectsAffineHyperplane A := by
  classical
  induction H using Finset.induction_on with
  | empty => exact ⟨K, hK, IsSubdivision.refl K, hN, by simp⟩
  | @insert A H _ ih =>
    obtain ⟨L, hL, hLK, hLN, hLH⟩ := ih
    obtain ⟨D, hD, hDL, hDN, hDA⟩ :=
      L.exists_locallyFinite_subdivision_respectsAffineHyperplane hL hLN A
    refine ⟨D, hD, hDL.trans hLK, hDN, ?_⟩
    intro B hB
    rcases Finset.mem_insert.mp hB with rfl | hB
    · exact hDA
    · exact hDL.respectsAffineHyperplane (hLH B hB)

end Geometry.SimplicialComplex
