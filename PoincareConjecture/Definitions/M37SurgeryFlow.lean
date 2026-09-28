import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Definitions.M33BranchContinuation
import PoincareConjecture.Definitions.M36MetricSurgery

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedSurgeryFlowData (g₀ : StandardInitialMetric) where
  flow : SurgeryFlowData.{u}
  standard_initial_eq : flow.standard_initial = g₀

structure RepairedSurgeryFlowCompatibilityData (g₀ : StandardInitialMetric)
    extends RepairedSurgeryFlowData.{u} g₀ where
  metric_surgery : RepairedMetricSurgeryData.{u} g₀
  constants_eq : metric_surgery.constants = flow.local_constants

  event_operation_input :
    ∀ (T : ℝ) (hT : T ∈ flow.surgery_times)
      [Nonempty (flow.slice T).carrier]
      (_i : Fin ((flow.event T hT).cap_count)),
      MetricSurgeryInput metric_surgery.constants
        (flow.event T hT).limit_metric
  event_operation_input_eq :
    ∀ (T : ℝ) (hT : T ∈ flow.surgery_times)
      [Nonempty (flow.slice T).carrier]
      (i : Fin ((flow.event T hT).cap_count)),
      HEq ((flow.event T hT).necks i) (event_operation_input T hT i)
  event_operation_alignment :
    ∀ (T : ℝ) (hT : T ∈ flow.surgery_times)
      [Nonempty (flow.slice T).carrier]
      (i : Fin ((flow.event T hT).cap_count)),
      HEq ((flow.event T hT).local_result i)
        (Classical.choice (metric_surgery.operation (event_operation_input T hT i)))
end PoincareConjecture
