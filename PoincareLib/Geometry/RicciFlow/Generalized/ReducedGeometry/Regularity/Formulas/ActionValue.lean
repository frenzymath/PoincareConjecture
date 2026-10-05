import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Theory

/-!
# Finite values and attainment on a stable branch

Morgan-Tian Definitions 6.26-6.27, p. 117, and Definition 6.45, p. 129.
These are the finite-value and stable-attainment fields of the frozen M14
conclusion. A stable branch already supplies an actual minimizing path.
-/

set_option autoImplicit false

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

/-- A nonempty action set bounded below has the finite-value output,
Morgan-Tian Definition 6.27, p. 117. -/
theorem finiteValueStatement (G : GeneralizedLGeometryTransport n X time I) :
    M14FiniteValueStatement G := by
  intro T τ₁ τ₂ x y h
  obtain ⟨a, ha⟩ := h.1
  exact ⟨M14ActionValue G T τ₁ τ₂ x y, rfl, a, ha, csInf_le h.2 ha⟩

/-- A stable minimizing branch attains its own action infimum,
Morgan-Tian Definitions 6.25-6.27, pp. 116-117. -/
theorem attainmentStatement (G : GeneralizedLGeometryTransport n X time I) :
    M14AttainmentStatement G := by
  intro T τ x E H Z hZ
  obtain ⟨p, hcurve, hp, _⟩ := H.minimizing_path Z hZ
  exact ⟨p, hcurve, hp, action_eq_actionValue_of_minimizing p hp⟩

end PoincareMT.M14
