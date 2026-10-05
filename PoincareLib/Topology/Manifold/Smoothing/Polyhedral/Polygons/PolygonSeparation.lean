import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonEdgeIntersections
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.DoubleCurve.PolygonCrossingJump

/-!
# Separation by a simple polygon

An isolated regular edge point supplies different values of the
locally constant crossing count on the complement. Consequently
that complement is not preconnected. This is the at-least-two
direction in Erickson, Simple Polygons, Section 1.2, p. 4;
see M76 derivation 96.
-/

set_option autoImplicit false

open Set

namespace Polygon

/-- The complement of a simple simplicial polygon with nonvertical
edges has a nonconstant signed ray count. See Erickson p. 4 and
M76 derivation 96. -/
theorem exists_crossingIndex_ne {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hnv : P.HasNonverticalEdges) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.crossingIndex a ≠ P.crossingIndex b := by
  obtain ⟨q, hq, hreg, hother⟩ := P.exists_regular_point_on_edge hP hinj hnv 0
  exact P.exists_crossingIndex_ne_of_isolated_edge hnv hq hreg hother

/-- The complement of a simple simplicial polygon with nonvertical
edges is not preconnected. This asserts separation, not that there
are exactly two components. See Erickson p. 4 and M76 derivation 96. -/
theorem not_isPreconnected_compl_of_nonvertical {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) (hnv : P.HasNonverticalEdges) :
    ¬ IsPreconnected (P.boundary ℝ)ᶜ := by
  intro h
  let : PreconnectedSpace ↥((P.boundary ℝ)ᶜ) := isPreconnected_iff_preconnectedSpace.mp h
  obtain ⟨a, ha, b, hb, hne⟩ := P.exists_crossingIndex_ne hP hinj hnv
  exact hne ((P.isLocallyConstant_crossingIndex hnv).apply_eq_of_preconnectedSpace
    (⟨a, ha⟩ : ↥((P.boundary ℝ)ᶜ)) ⟨b, hb⟩)

end Polygon
