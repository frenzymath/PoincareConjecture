import PoincareLib.Geometry.RicciFlow.Surgery.Flow.Basic
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Branch
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.OperationData

/-!
Adapted from Mapher `PoincareMT/Definitions/M37SurgeryFlow.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M37 repaired changing-carrier surgery-flow data

The core view retains the actual event maps, retained regions, inserted
caps, discarded components, and empty terminal slices. Optional M36 operation
provenance lives in a separate compatibility extension.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-! The core changing-carrier view is intentionally independent of the M36
operation witness. Every later topology and width consumer uses only this
primitive flow/index pair. -/
structure RepairedSurgeryFlowData (g₀ : StandardInitialMetric) where
  flow : SurgeryFlowData.{u}
  standard_initial_eq : flow.standard_initial = g₀

/-! M37 keeps the optional operation provenance in a separate extension. The
raw global flow does not acquire this data merely by being reindexed. -/
structure RepairedSurgeryFlowCompatibilityData (g₀ : StandardInitialMetric)
    extends RepairedSurgeryFlowData.{u} g₀ where
  metric_surgery : RepairedMetricSurgeryData.{u} g₀
  constants_eq : metric_surgery.constants = flow.local_constants
  /-- Each selected event result is the result supplied by M36 after
      transporting the event constants across `constants_eq`. -/
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
end PoincareMT
