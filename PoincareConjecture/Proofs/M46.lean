import PoincareConjecture.Statements.M46NoncollapseInduction
import PoincareConjecture.Proofs.M46.GuardedVolume
import PoincareConjecture.Proofs.M46.ConfigurationTransfer
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_1_CapAvoidance
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_1_FinalAssembly

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedNoncollapseInduction (predecessors : M46Predecessors.{u}) :
    RepairedNoncollapseInductionTheory.{u} := by
  refine ⟨fun S => ?_⟩
  exact Proofs.M46.induction_of_actionBarrierProducer predecessors S
    (Proofs.M46.capAvoidanceProducer_of_parameters predecessors S)

end PoincareConjecture
