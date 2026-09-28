import PoincareConjecture.Proofs.M47.Providers
import PoincareConjecture.Proofs.M04.CurvatureCalculus
import PoincareConjecture.Proofs.M04.ScalarEvolution









set_option autoImplicit false

universe u

namespace PoincareConjecture


theorem m47ScalarPersistencePredecessors_from_M04 :
    M47ScalarPersistencePredecessors.{u} := {
  tensor_calculus := @LeviCivitaData.curvatureTensorCalculus 3
  scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature 3
  scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature 3
}


theorem m47LocalScalarPersistence_from_predecessors
    (C : RepairedCanonicalInductionTheory.{u})
    (P : M47ScalarPersistencePredecessors.{u}) :
    M47LocalScalarPersistenceStatement.{u} :=
  C.local_scalar_persistence P


theorem m47LocalScalarPersistenceFromMilestones :
    M47LocalScalarPersistenceStatement.{u} :=
  m47LocalScalarPersistence_from_predecessors m47CanonicalInductionFromMilestones
    m47ScalarPersistencePredecessors_from_M04

end PoincareConjecture
