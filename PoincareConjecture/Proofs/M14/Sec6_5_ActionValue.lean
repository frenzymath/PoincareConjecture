import PoincareConjecture.Proofs.M14.Sec6_1_LLength
import PoincareConjecture.Statements.M14GeneralizedLGeometry

set_option autoImplicit false

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval}

theorem finiteValueStatement (G : GeneralizedLGeometryTransport n X time I) :
    M14FiniteValueStatement G := by
  intro T τ₁ τ₂ x y h
  obtain ⟨a, ha⟩ := h.1
  exact ⟨M14ActionValue G T τ₁ τ₂ x y, rfl, a, ha, csInf_le h.2 ha⟩

theorem attainmentStatement (G : GeneralizedLGeometryTransport n X time I) :
    M14AttainmentStatement G := by
  intro T τ x E H Z hZ
  obtain ⟨p, hcurve, hp, _⟩ := H.minimizing_path Z hZ
  exact ⟨p, hcurve, hp, action_eq_actionValue_of_minimizing p hp⟩

end PoincareConjecture.M14
