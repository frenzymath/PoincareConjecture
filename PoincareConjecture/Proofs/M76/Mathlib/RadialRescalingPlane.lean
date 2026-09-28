import PoincareConjecture.Proofs.M76.Mathlib.RadialRescalingHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.HyperplaneSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.AffineZeroFaceHull

set_option autoImplicit false

open Set Geometry

namespace Finset

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem affine_eq_zero_iff_of_vertex_zeros (s : Finset E)
    (A B : E →ᵃ[ℝ] ℝ) (hA : ∀ v ∈ s, 0 ≤ A v) (hB : ∀ v ∈ s, 0 ≤ B v)
    (hzero : ∀ v ∈ s, A v = 0 ↔ B v = 0) {x : E}
    (hx : x ∈ convexHull ℝ (s : Set E)) : A x = 0 ↔ B x = 0 := by
  constructor
  · intro hAx
    have hz := s.mem_convexHull_zero_vertices A hA hx hAx
    exact convexHull_min (fun v hv => (hzero v hv.1).mp hv.2)
      ((convex_singleton (0 : ℝ)).affine_preimage B) hz
  · intro hBx
    have hz := s.mem_convexHull_zero_vertices B hB hx hBx
    exact convexHull_min (fun v hv => (hzero v hv.1).mpr hv.2)
      ((convex_singleton (0 : ℝ)).affine_preimage A) hz

end Finset

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : SimplicialComplex ℝ E} {f : E → E}

theorem AffineOnFaces.linear_zero_iff_of_positive_vertex_rescaling
    (hf : K.AffineOnFaces f) (r : E → ℝ) (hr : ∀ x ∈ K.vertices, 0 < r x)
    (hvertex : EqOn f (fun x => r x • x) K.vertices)
    (C : E →ₗ[ℝ] ℝ) (hC : K.RespectsAffineHyperplane C.toAffineMap) :
    ∀ x ∈ K.space, C (f x) = 0 ↔ C x = 0 := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨a, ha⟩ := hf s hs
  have hpositive (L : E →ₗ[ℝ] ℝ) (hL : ∀ v ∈ s, 0 ≤ L v) :
      L (f x) = 0 ↔ L x = 0 := by
    have hval (v : E) (hv : v ∈ s) : L (a v) = r v * L v := by
      rw [← ha (subset_convexHull ℝ _ hv), hvertex (K.face_subset_vertices hs hv),
        map_smul, smul_eq_mul]
    have hLa (v : E) (hv : v ∈ s) : 0 ≤ L (a v) := by
      rw [hval v hv]
      exact mul_nonneg (hr v (K.face_subset_vertices hs hv)).le (hL v hv)
    have hzeros (v : E) (hv : v ∈ s) : L (a v) = 0 ↔ L v = 0 := by
      rw [hval v hv]
      simp only [mul_eq_zero, (hr v (K.face_subset_vertices hs hv)).ne', false_or]
    have h := s.affine_eq_zero_iff_of_vertex_zeros
      (L.toAffineMap.comp a.toAffineMap) L.toAffineMap hLa hL hzeros hxs
    change L (a x) = 0 ↔ L x = 0 at h
    rwa [← ha hxs] at h
  rcases hC s hs with hneg | hpos
  · have h := hpositive (-C) (fun v hv =>
      neg_nonneg.mpr (hneg v (subset_convexHull ℝ _ hv)))
    simpa only [LinearMap.neg_apply, neg_eq_zero] using h
  · exact hpositive C (fun v hv => hpos v (subset_convexHull ℝ _ hv))

end Geometry.SimplicialComplex
