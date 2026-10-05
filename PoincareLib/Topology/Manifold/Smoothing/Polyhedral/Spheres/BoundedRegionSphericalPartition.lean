import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Spheres.BoundedRegionSphericalFrontier

/-!
# Actual spherical covering and boundary intersections

An open region and its top-face closure determine a spherical
cover whose overlap is exactly the embedded frontier. These
identities instantiate the ball-pair collar constructions.
See Alexander 1924, p. 7 and M76 derivation 247.
-/

set_option autoImplicit false

open Set

namespace Set

variable {X : Type*} [TopologicalSpace X]

/-- A region's top-face closure and its spherical exterior
cover the entire cylinder frontier. See Alexander p. 7
and M76 derivation 247. -/
theorem top_face_union_cylinderExterior {U D : Set X} (hUD : closure U ⊆ D) :
    (closure U ×ˢ {(1 : ℝ)}) ∪
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) =
      frontier (D ×ˢ Icc (-1 : ℝ) 1) := by
  apply Subset.antisymm
    (union_subset (prod_singleton_one_subset_frontier_cylinder hUD) sdiff_subset)
  intro x hx
  by_cases hxU : x ∈ U ×ˢ {(1 : ℝ)}
  · exact Or.inl ⟨subset_closure hxU.1, hxU.2⟩
  · exact Or.inr ⟨hx, hxU⟩

/-- The actual overlap of a top-face region closure and its
spherical exterior is its entire embedded frontier.
See Alexander p. 7 and M76 derivation 247. -/
theorem top_face_inter_cylinderExterior {U D : Set X}
    (hU : IsOpen U) (hUD : closure U ⊆ D) :
    (closure U ×ˢ {(1 : ℝ)}) ∩
        (frontier (D ×ˢ Icc (-1 : ℝ) 1) \ U ×ˢ {1}) =
      frontier U ×ˢ {1} := by
  have hUS := prod_singleton_one_subset_frontier_cylinder hUD
  rw [show frontier U = closure U \ U from by rw [frontier, hU.interior_eq]]
  ext x
  constructor
  · rintro ⟨hxU, _, hxnot⟩
    exact ⟨⟨hxU.1, fun hx => hxnot ⟨hx, hxU.2⟩⟩, hxU.2⟩
  · rintro ⟨⟨hxU, hxnot⟩, hxone⟩
    exact ⟨⟨hxU, hxone⟩, hUS ⟨hxU, hxone⟩, fun hx => hxnot hx.1⟩

end Set
