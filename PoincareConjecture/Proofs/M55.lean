import PoincareConjecture.Statements.M55ChildComponents
import PoincareConjecture.Proofs.M55.Components

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedChildComponents : RepairedChildComponentsTheory.{u} := by
  refine ⟨fun _G54 {_A _B} _C E _hE parent_groups_subsingleton => ?_⟩
  exact ⟨E.childComponents parent_groups_subsingleton⟩

end PoincareConjecture
