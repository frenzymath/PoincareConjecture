import PoincareConjecture.Statements.M41NonemptyContinuation

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedNonemptyContinuation : RepairedNonemptyContinuationTheory.{u} := by
  refine ⟨?_⟩
  intro F T I branch hcore
  have hpost : Nonempty (branch.conclusion.extension.extended.slice T).carrier :=
    (branch.conclusion.terminal_nonempty_iff).mp hcore
  cases hoperation : branch.conclusion.terminal_operation with
  | nonempty hpost' operation =>
      exact ⟨⟨hpost', operation, hoperation, branch.conclusion.post_terminal_interval,
        branch.conclusion.admissible, branch.conclusion.pinched⟩⟩
  | vanishing hempty _operation =>
      cases hpost with
      | intro x => exact (hempty.false x).elim

end PoincareConjecture
