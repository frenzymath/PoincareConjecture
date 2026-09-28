import PoincareConjecture.Proofs.M04
import PoincareConjecture.Proofs.M13
import PoincareConjecture.Proofs.M44









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

theorem m44CapPersistencePredecessorsFromMilestones :
    M44CapPersistencePredecessors.{u} :=
  {
    curvature := ricciFlowCurvatureTheory
    ordinary_flow := (generalizedParabolicRescaling_from_M12 3).ordinary_flow
  }

theorem m44CapPersistenceFromMilestones :
    RepairedCapPersistenceTheory.{u} :=
  repairedCapPersistence m44CapPersistencePredecessorsFromMilestones

end PoincareConjecture
