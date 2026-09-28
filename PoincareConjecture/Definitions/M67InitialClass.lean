import PoincareConjecture.Definitions.M67
import PoincareConjecture.Statements.M59LoopIdentification










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def m67InitialTime {F : SurgeryFlowData.{u}} {T : ℝ}
    {W : RepairedEventChildWitness F} (P : RepairedComponentPath F T W) :
    Set.Icc (0 : ℝ) T :=
  ⟨0, le_rfl, F.time_domain_nonnegative P.terminal_mem⟩

structure M67InitialClassData (S : M59IdentificationSystem.{u})
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (ambient_metric : RiemannianMetric 3 A.carrier) where
  metric : RiemannianMetric 3 C.carrier.carrier
  metric_pullback : ∀ x v w,
    ambient_metric.inner (C.inclusion x)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) = metric.inner x v w
  pi_two_trivial : Subsingleton (HomotopyGroup.Pi 2 C.carrier.carrier C.basepoint)
  alpha : HomotopyGroup.Pi 2 (C1FreeLoopSpace (M := C.carrier.carrier))
    (constantC1Loop C.basepoint)
  nonzero : (S.core C.compact C.connected C.basepoint pi_two_trivial).pi_two_pi_three
    alpha ≠ 1

end PoincareConjecture
