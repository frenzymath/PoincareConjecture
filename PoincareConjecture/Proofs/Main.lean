import PoincareConjecture.Proofs.M90

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem smoothPoincareSkeleton : SmoothPoincare.{u} := by
  exact m75SmoothPoincare m90SmoothEndpointInputs

theorem topologicalPoincareSkeleton : TopologicalPoincare.{u} := by
  obtain ⟨C⟩ := m90FinalAssemblyFromMilestones.{u}
  exact C.topological

end PoincareConjecture
