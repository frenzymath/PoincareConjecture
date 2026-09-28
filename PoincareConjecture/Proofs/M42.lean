import PoincareConjecture.Statements.M42VanishingContinuation








set_option autoImplicit false

universe u

namespace PoincareConjecture






















theorem repairedVanishingContinuation : RepairedVanishingContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro F T I branch hcore
  have hempty : IsEmpty (branch.conclusion.extension.extended.slice T).carrier :=
    (branch.conclusion.terminal_empty_iff).mp hcore
  cases hoperation : branch.conclusion.terminal_operation with
  | nonempty hpost _operation =>
      cases hpost with
      | intro x => exact (hempty.false x).elim
  | vanishing hempty' operation =>
      exact ⟨⟨hempty', operation, hoperation,
        branch.conclusion.terminal_empty_end_time_top hcore,
        branch.conclusion.post_terminal_interval,
        branch.conclusion.admissible, branch.conclusion.pinched⟩⟩

end PoincareConjecture
