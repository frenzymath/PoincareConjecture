import PoincareConjecture.Statements.M47CanonicalInduction
import PoincareConjecture.Proofs.M47.CanonicalControls
import PoincareConjecture.Proofs.M47.RegularHistory
import PoincareConjecture.Proofs.M47.TerminalComponents
import PoincareConjecture.Proofs.M47.InductionCompletion

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedCanonicalInduction (P : M47Predecessors.{u}) :
    RepairedCanonicalInductionTheory.{u} :=
  Proofs.M47.canonicalInductionTheory_of_induction P (M47.canonicalInduction P)

end PoincareConjecture
