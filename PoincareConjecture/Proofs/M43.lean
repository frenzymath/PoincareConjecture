import PoincareConjecture.Statements.M43UnifiedContinuation

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedUnifiedContinuation : RepairedUnifiedContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro N V F T I branch
  cases I.core_status with
  | nonempty hcore =>
      rcases N.continuation I branch hcore with ⟨continuation⟩
      exact ⟨⟨Sum.inl continuation⟩⟩
  | empty hcore =>
      rcases V.continuation I branch hcore with ⟨continuation⟩
      exact ⟨⟨Sum.inr continuation⟩⟩

end PoincareConjecture
