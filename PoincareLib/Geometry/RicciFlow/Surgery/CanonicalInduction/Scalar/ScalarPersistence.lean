import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Providers
import PoincareLib.Geometry.Riemannian.Curvature.IntrinsicCalculus
import PoincareLib.Geometry.RicciFlow.Curvature.Evolution.Scalar.Within

/-!
# Applied M04 inputs for M47 local scalar persistence

These proofs supply actual earlier theorem services without a new admission.
The local cutoff/comparison construction remains part of M47's single
placeholder. This application does not establish a surgery analytic estimate.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

/-- Apply the three M04 components on each actual dimension-three input. -/
theorem m47ScalarPersistencePredecessors_from_M04 :
    M47ScalarPersistencePredecessors.{u} := {
  tensor_calculus := @LeviCivitaData.curvatureTensorCalculus 3
  scalar_regular := @RicciFlow.contMDiffOn_scalarCurvature 3
  scalar_evolution := @RicciFlow.hasDerivWithinAt_scalarCurvature 3
}

/-- Use the selected M47 support with the explicitly supplied M04 services. -/
theorem m47LocalScalarPersistence_from_predecessors
    (C : RepairedCanonicalInductionTheory.{u})
    (P : M47ScalarPersistencePredecessors.{u}) :
    M47LocalScalarPersistenceStatement.{u} :=
  C.local_scalar_persistence P

/-- The primitive local conclusion from the actual M04 and M47 milestones. -/
theorem m47LocalScalarPersistenceFromMilestones :
    M47LocalScalarPersistenceStatement.{u} :=
  m47LocalScalarPersistence_from_predecessors m47CanonicalInductionFromMilestones
    m47ScalarPersistencePredecessors_from_M04

end PoincareMT
