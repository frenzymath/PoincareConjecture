import PoincareConjecture.Proofs.M90

/-! The final assembly of the smooth and topological Poincare theorems. -/

set_option autoImplicit false

universe u

namespace PoincareConjecture

/-- A compact simply connected smooth three-manifold is diffeomorphic to the
standard three-sphere. -/
theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact m75SmoothPoincare m90SmoothEndpointInputs

/-- A compact simply connected topological three-manifold is homeomorphic to
the standard three-sphere. -/
theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  obtain ⟨C⟩ := m90FinalAssemblyFromMilestones.{u}
  exact C.topological

end PoincareConjecture
