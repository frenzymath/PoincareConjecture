import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingPlane

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → E}

theorem AffineOnFaces.linear_nonneg_iff_of_positive_vertex_rescaling
    (hf : K.AffineOnFaces f) (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hvertex : EqOn f (fun x => r x • x) K.vertices)
    (C : E →ₗ[ℝ] ℝ) (hC : K.RespectsAffineHyperplane C.toAffineMap) :
    ∀ x ∈ K.space, 0 ≤ C (f x) ↔ 0 ≤ C x := by
  intro x hx
  have hzero := hf.linear_zero_iff_of_positive_vertex_rescaling r hr hvertex C hC x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  have hpositive (L : E →ₗ[ℝ] ℝ) (hL : ∀ v ∈ s, 0 ≤ L v) : 0 ≤ L (f x) := by
    rw [ha hxs]
    apply convexHull_min (t := (L.toAffineMap.comp a.toAffineMap) ⁻¹' Ici 0) ?_
      ((convex_Ici (0 : ℝ)).affine_preimage (L.toAffineMap.comp a.toAffineMap)) hxs
    intro v hv
    change 0 ≤ L (a v)
    rw [← ha (subset_convexHull ℝ _ hv), hvertex (K.face_subset_vertices hs hv),
      map_smul, smul_eq_mul]
    exact mul_nonneg (hr v (K.face_subset_vertices hs hv)).le (hL v hv)
  rcases hC s hs with hneg | hpos
  · have hnx : C x ≤ 0 := hneg x hxs
    have hnf : C (f x) ≤ 0 := by
      have h := hpositive (-C) (fun v hv =>
        neg_nonneg.mpr (hneg v (subset_convexHull ℝ _ hv)))
      exact neg_nonneg.mp h
    constructor
    · intro h
      exact (hzero.mp (le_antisymm hnf h)).ge
    · intro h
      exact (hzero.mpr (le_antisymm hnx h)).ge
  · exact iff_of_true
      (hpositive C (fun v hv => hpos v (subset_convexHull ℝ _ hv))) (hpos x hxs)

end Geometry.SimplicialComplex
