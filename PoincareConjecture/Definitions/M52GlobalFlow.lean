import PoincareConjecture.Definitions.Ch17.GlobalSurgery
import PoincareConjecture.Definitions.M51GlobalSchedule

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedGlobalFlowData
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M]
    (N : NormalizedInitialMetric (M := M)) where
  schedule : RepairedGlobalScheduleData N
  certificate : GlobalSurgeryFlowCertificate N
  flow_eq : certificate.flow = schedule.flow
  schedule_eq : HEq certificate.schedule schedule.schedule
  control_function_eq : certificate.control_function = schedule.control_function
end PoincareConjecture
