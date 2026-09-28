import PoincareConjecture.Definitions.Ch16.NoncollapseInduction
import PoincareConjecture.Definitions.M45ControlledSchedules

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedNoncollapseInductionData
    (S : RepairedControlledSchedulesData.{u}) where
  induction : ∀ p : SurgeryParameterPrefix S.constants,
    S.SeedCompatible p → Nonempty (SurgeryNoncollapseExtension.{u} p)

def OldTestedVolumeControls {K : MetricSurgeryConstants}
    (p : SurgeryParameterPrefix K)
    (F : SurgeryFlowData.{u}) (O : SurgeryObservation F) : Prop :=
  SurgeryTestedVolumeOn F
    (surgeryObservationInterval O ∩ surgeryEpochEntry p.i)
    (p.kappa ⟨p.i, Nat.lt_succ_self _⟩)
    (p.r ⟨p.i, Nat.lt_succ_self _⟩) 16

end PoincareConjecture
