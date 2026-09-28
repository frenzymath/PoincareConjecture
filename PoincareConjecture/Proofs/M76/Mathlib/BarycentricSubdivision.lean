import PoincareConjecture.Proofs.M76.Mathlib.DerivedSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.CentroidMesh










set_option autoImplicit false

open Set Metric
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]

omit [Fintype K.faces] in
private theorem centroid_positive_weights (s : K.faces) :
    ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧ (∑ v ∈ s.val, w v) = 1 ∧
      (∑ v ∈ s.val, w v • v) = s.val.centroid ℝ id := by
  have hs := K.nonempty_of_mem_faces s.property
  refine ⟨s.val.centroidWeights ℝ, ?_,
    s.val.sum_centroidWeights_eq_one_of_nonempty ℝ hs, ?_⟩
  · intro v _
    simp only [Finset.centroidWeights_apply, inv_pos]
    exact_mod_cast hs.card_pos
  · rw [Finset.centroid_eq_inv_card_smul_sum _ hs]
    simp only [Finset.centroidWeights_apply, Finset.smul_sum, id_eq]



noncomputable def barycentricSubdivision : SimplicialComplex ℝ E :=
  K.derivedSubdivision (fun s => s.val.centroid ℝ id) K.centroid_positive_weights



theorem barycentricSubdivision_finite : K.barycentricSubdivision.faces.Finite :=
  K.derivedSubdivision_finite _ _



theorem barycentricSubdivision_isSubdivision : K.barycentricSubdivision.IsSubdivision K :=
  K.derivedSubdivision_isSubdivision _ _



theorem barycentricSubdivision_card_le {N : ℕ}
    (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) :
    ∀ s ∈ K.barycentricSubdivision.faces, s.card ≤ N + 1 :=
  K.derivedSubdivision_card_le _ _ hN



theorem barycentricSubdivision_diam_le {N : ℕ}
    (hN : ∀ s ∈ K.faces, s.card ≤ N + 1) {D : ℝ} (hD : 0 ≤ D)
    (hdiam : ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D) :
    ∀ s ∈ K.barycentricSubdivision.faces,
      diam (convexHull ℝ (s : Set E)) ≤ (N : ℝ) / ((N : ℝ) + 1) * D := by
  classical
  intro t ht
  obtain ⟨s, _, hchain, rfl⟩ :=
    (K.derivedSubdivision_faces _ K.centroid_positive_weights t).mp ht
  rw [convexHull_diam]
  apply diam_le_of_forall_dist_le (by positivity)
  intro x hx y hy
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  rcases hchain i hi j hj with hij | hji
  · exact Finset.dist_centroid_le_mesh_factor (K.nonempty_of_mem_faces i.property) hij
      (hN j.val j.property) hD (hdiam j.val j.property)
  · rw [dist_comm]
    exact Finset.dist_centroid_le_mesh_factor (K.nonempty_of_mem_faces j.property) hji
      (hN i.val i.property) hD (hdiam i.val i.property)

end Geometry.SimplicialComplex
