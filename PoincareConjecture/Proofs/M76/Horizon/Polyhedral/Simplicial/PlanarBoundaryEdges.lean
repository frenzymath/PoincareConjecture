import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.PlanarTriangleBoundaries
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation









set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]

theorem frontier_point_vertex_or_boundary_edge
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hdim : Module.finrank ℝ E = 2) (hcv : Convex ℝ K.space)
    (hne : (interior K.space).Nonempty) {x : E} (hx : x ∈ frontier K.space) :
    x ∈ K.vertices ∨ ∃ a b : E, a ≠ b ∧ ({a, b} : Finset E) ∈ K.faces ∧
      a ∈ frontier K.space ∧ b ∈ frontier K.space ∧ x ∈ openSegment ℝ a b := by
  have hxK : x ∈ K.space := (K.isCompact_space_of_finite hK).isClosed.closure_eq ▸ hx.1
  obtain ⟨t, ht, htc, hxt⟩ := K.exists_full_face_of_mem_convex_space hK hcv hne hxK
  have ht3 : t.card = 3 := by omega
  have hxf : x ∈ frontier (convexHull ℝ (t : Set E)) :=
    ⟨subset_closure hxt, fun h => hx.2 (interior_mono (K.convexHull_subset_space ht) h)⟩
  rw [K.triangle_frontier_eq_iUnion_erase hdim ht ht3] at hxf
  obtain ⟨p, hp⟩ := mem_iUnion.mp hxf
  obtain ⟨he, hec, _⟩ := K.triangle_erase_is_edge ht ht3 p.property
  obtain ⟨a, b, hab, heq⟩ := Finset.card_eq_two.mp hec
  rw [heq] at he hp
  have hseg : x ∈ segment ℝ a b := by simpa only [Finset.coe_pair, convexHull_pair] using hp
  have haK : a ∈ K.space := K.convexHull_subset_space he (subset_convexHull ℝ _ (by simp))
  have hbK : b ∈ K.space := K.convexHull_subset_space he (subset_convexHull ℝ _ (by simp))
  by_cases hax : a = x
  · exact Or.inl (hax ▸ K.down_closed he (by simp) (Finset.singleton_nonempty a))
  by_cases hbx : b = x
  · exact Or.inl (hbx ▸ K.down_closed he (by simp) (Finset.singleton_nonempty b))
  have hopen : x ∈ openSegment ℝ a b := mem_openSegment_of_ne_left_right hax hbx hseg
  refine Or.inr ⟨a, b, hab, he, ⟨subset_closure haK, ?_⟩, ⟨subset_closure hbK, ?_⟩, hopen⟩
  · intro ha
    exact hx.2 (hcv.openSegment_interior_self_subset_interior ha hbK hopen)
  · intro hb
    exact hx.2 (hcv.openSegment_self_interior_subset_interior haK hb hopen)

end Geometry.SimplicialComplex
