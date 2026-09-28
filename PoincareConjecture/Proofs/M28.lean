import PoincareConjecture.Statements.M28BoundedDistance
import PoincareConjecture.Statements.M28Providers
import PoincareConjecture.Proofs.M28.Thm10_2_Exclusion
import PoincareConjecture.Proofs.M28.Thm10_2_SameTime

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m28BoundedDistance (P : M28BoundedDistancePredecessors.{u}) :
    RepairedBoundedDistanceTheory.{u} := by
  obtain ⟨epsilon0, hpositive, hsmall, hexclude⟩ :=
    M28.exists_actual_counterexample_exclusion_accuracy P.m04 (Classical.choice P.m25)
  exact M28.theory_of_counterexample_exclusion P.m04 hpositive hsmall hexclude

end PoincareConjecture
