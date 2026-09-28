import PoincareConjecture.Proofs.M34.Providers
import PoincareConjecture.Proofs.M34.Assembly
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.UnitLifetime

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

theorem repairedStandardCapExistence_of_predecessors
    (P : M34StandardCapPredecessors) : RepairedStandardCapExistenceTheory := by
  exact M34.repairedStandardCapExistenceTheory_of_lifetime_ge_one P
    (fun _ F => M34.standardFlow_lifetime_ge_one P F)

theorem repairedStandardCapExistence : RepairedStandardCapExistenceTheory :=
  repairedStandardCapExistence_of_predecessors m34StandardCapPredecessorsFromMilestones

end PoincareConjecture
