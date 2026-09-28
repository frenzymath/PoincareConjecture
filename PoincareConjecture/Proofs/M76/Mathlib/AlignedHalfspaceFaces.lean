import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.AffineFaceMaps

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_face_in_halfspaces (K : SimplicialComplex ℝ E)
    (H : Finset (E →ᵃ[ℝ] ℝ)) (hH : ∀ A ∈ H, K.RespectsAffineHyperplane A)
    {x : E} (hx : x ∈ K.space) (hxH : ∀ A ∈ H, A x ≤ 0) :
    ∃ s ∈ K.faces, x ∈ convexHull ℝ (s : Set E) ∧ ∀ v ∈ s, ∀ A ∈ H, A v ≤ 0 := by
  classical
  induction H using Finset.induction_on with
  | empty =>
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact ⟨s, hs, hxs, by simp⟩
  | @insert A H _ ih =>
    obtain ⟨s, hs, hxs, hverts⟩ := ih
      (fun B hB => hH B (Finset.mem_insert_of_mem hB))
      (fun B hB => hxH B (Finset.mem_insert_of_mem hB))
    rcases hH A (Finset.mem_insert_self A H) s hs with h | h
    · refine ⟨s, hs, hxs, fun v hv B hB => ?_⟩
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact h v (subset_convexHull ℝ _ hv)
      · exact hverts v hv B hB
    · have hAx : A x = 0 := le_antisymm (hxH A (Finset.mem_insert_self A H)) (h x hxs)
      let t := s.filter (fun v => A v = 0)
      have hxt : x ∈ convexHull ℝ (t : Set E) := by
        have he : (t : Set E) = (s : Set E) ∩ {v | A v = 0} := by
          ext v
          simp only [t, Finset.mem_coe, Finset.mem_filter, mem_inter_iff, mem_ofPred_eq]
        rw [he]
        exact s.mem_convexHull_zero_vertices A
          (fun v hv => h v (subset_convexHull ℝ _ hv)) hxs hAx
      have htne : t.Nonempty :=
        Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨x, hxt⟩)
      refine ⟨t, K.down_closed hs (Finset.filter_subset _ _) htne, hxt, fun v hv B hB => ?_⟩
      rcases Finset.mem_insert.mp hB with rfl | hB
      · exact (Finset.mem_filter.mp hv).2.le
      · exact hverts v (Finset.mem_filter.mp hv).1 B hB

theorem AffineOnFaces.mapsTo_of_aligned_halfspaces {K : SimplicialComplex ℝ E}
    {f : E → F} (hf : K.AffineOnFaces f) (H : Finset (E →ᵃ[ℝ] ℝ))
    (hH : ∀ A ∈ H, K.RespectsAffineHyperplane A) {T : Set F} (hT : Convex ℝ T)
    (hv : ∀ v ∈ K.vertices, (∀ A ∈ H, A v ≤ 0) → f v ∈ T) :
    ∀ x ∈ K.space, (∀ A ∈ H, A x ≤ 0) → f x ∈ T := by
  intro x hx hxH
  obtain ⟨s, hs, hxs, hverts⟩ := K.exists_face_in_halfspaces H hH hx hxH
  have hsverts : (s : Set E) ⊆ K.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  have himage : f '' (s : Set E) ⊆ T := by
    rintro _ ⟨v, hvS, rfl⟩
    exact hv v (hsverts hvS) (hverts v hvS)
  exact convexHull_min himage hT (hf.mapsTo_convexHull hs Subset.rfl hxs)

end Geometry.SimplicialComplex
