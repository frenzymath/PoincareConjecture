import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph
import Mathlib.Data.Finset.Max

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mem_both_height_closures_of_not_mem_vertex_heights
    (K : SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] ℝ)
    {x : E} (hx : x ∈ K.space) (hheight : A x ∉ A '' K.vertices) :
    x ∈ closure (K.space ∩ {y | A y < A x}) ∧
      x ∈ closure (K.space ∩ {y | A x < A y}) := by
  classical
  obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
  obtain ⟨v, hv, hmin⟩ := s.exists_min_image A (K.nonempty_of_mem_faces hs)
  obtain ⟨w, hw, hmax⟩ := s.exists_max_image A (K.nonempty_of_mem_faces hs)
  have hvK : v ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty _)
  have hwK : w ∈ K.vertices :=
    K.down_closed hs (Finset.singleton_subset_iff.mpr hw) (Finset.singleton_nonempty _)
  have hlo : A v ≤ A x :=
    convexHull_min (fun y hy => hmin y hy) ((convex_Ici (A v)).affine_preimage A) hxs
  have hhi : A x ≤ A w :=
    convexHull_min (fun y hy => hmax y hy) ((convex_Iic (A w)).affine_preimage A) hxs
  have hlostrict : A v < A x :=
    lt_of_le_of_ne hlo (fun h => hheight ⟨v, hvK, h⟩)
  have hhistrict : A x < A w :=
    lt_of_le_of_ne hhi (fun h => hheight ⟨w, hwK, h.symm⟩)
  have hface : convexHull ℝ (s : Set E) ⊆ K.space := K.convexHull_subset_space hs
  have hlower := (convex_convexHull ℝ (s : Set E)).mem_closure_lower_affine_height A
    hxs (subset_convexHull ℝ _ hv) hlostrict
  have hupper := (convex_convexHull ℝ (s : Set E)).mem_closure_upper_affine_height A
    hxs (subset_convexHull ℝ _ hw) hhistrict
  exact ⟨closure_mono (inter_subset_inter_left _ hface) hlower,
    closure_mono (inter_subset_inter_left _ hface) hupper⟩

theorem finite_exceptional_vertex_height_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (A : E →ᵃ[ℝ] ℝ) :
    (A '' K.vertices).Finite ∧
      ∀ x ∈ K.space, A x ∉ A '' K.vertices →
        x ∈ closure (K.space ∩ {y | A y < A x}) ∧
          x ∈ closure (K.space ∩ {y | A x < A y}) := by
  classical
  exact ⟨(K.finite_vertices_of_finite_faces hK).image A,
    fun _ hx hheight => K.mem_both_height_closures_of_not_mem_vertex_heights A hx hheight⟩

end Geometry.SimplicialComplex
