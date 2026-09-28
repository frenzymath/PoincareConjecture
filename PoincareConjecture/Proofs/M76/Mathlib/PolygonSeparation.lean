import PoincareConjecture.Proofs.M76.Mathlib.PolygonEdgeIntersections
import PoincareConjecture.Proofs.M76.Mathlib.PolygonCrossingJump











set_option autoImplicit false

open Set

namespace Polygon




theorem exists_crossingIndex_ne {n : ℕ} (P : Polygon (ℝ × ℝ) (n + 3))
    (hP : P.HasSimplicialEdges) (hinj : Function.Injective P)
    (hnv : P.HasNonverticalEdges) :
    ∃ a ∈ (P.boundary ℝ)ᶜ, ∃ b ∈ (P.boundary ℝ)ᶜ,
      P.crossingIndex a ≠ P.crossingIndex b := by
  obtain ⟨q, hq, hreg, hother⟩ := P.exists_regular_point_on_edge hP hinj hnv 0
  exact P.exists_crossingIndex_ne_of_isolated_edge hnv hq hreg hother




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
