import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull
import PoincareConjecture.Proofs.M76.Mathlib.AffineOnFaces
import Mathlib.Tactic.Linarith











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → E}





theorem AffineOnFaces.eqOn_core_of_sectors (hf : K.AffineOnFaces f)
    (hsector : ∀ s ∈ K.faces,
      (∀ x ∈ convexHull ℝ (s : Set E), ‖x‖ ≤ 1) ∨
      ∃ L : E →ₗ[ℝ] ℝ, ∀ x ∈ convexHull ℝ (s : Set E), 1 ≤ L x ∧ ‖x‖ = L x)
    (hfix : ∀ v ∈ K.vertices, ‖v‖ ≤ 1 → f v = v) :
    ∀ x ∈ K.space, ‖x‖ ≤ 1 → f x = x := by
  intro x hx hxnorm
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  have hvertices : (s : Set E) ⊆ K.vertices := by
    rw [vertices_eq]
    exact subset_biUnion_of_mem hs
  have hfixed {T : Set E} (hTs : T ⊆ (s : Set E))
      (hTcore : ∀ v ∈ T, ‖v‖ ≤ 1) (hxT : x ∈ convexHull ℝ T) : f x = x := by
    have hEq : EqOn a.toAffineMap (AffineMap.id ℝ E) T := by
      intro v hv
      exact (ha (subset_convexHull ℝ _ (hTs hv))).symm.trans
        (hfix v (hvertices (hTs hv)) (hTcore v hv))
    exact (ha hxs).trans (AffineMap.eqOn_affineSpan hEq (convexHull_subset_affineSpan _ hxT))
  rcases hsector s hs with hcore | ⟨L, hL⟩
  · exact hfixed Subset.rfl (fun v hv => hcore v (subset_convexHull ℝ _ hv)) hxs
  · let A : E →ᵃ[ℝ] ℝ := L.toAffineMap - AffineMap.const ℝ E 1
    have hA (v : E) (hv : v ∈ s) : 0 ≤ A v :=
      sub_nonneg.mpr (hL v (subset_convexHull ℝ _ hv)).1
    have hAx : A x = 0 := by
      change L x - 1 = 0
      obtain ⟨hxL, he⟩ := hL x hxs
      linarith
    apply hfixed inter_subset_left _ (s.mem_convexHull_zero_vertices A hA hxs hAx)
    intro v hv
    have he : L v - 1 = 0 := hv.2
    rw [(hL v (subset_convexHull ℝ _ hv.1)).2]
    linarith

end Geometry.SimplicialComplex
