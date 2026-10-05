import PoincareLib.Geometry.RicciFlow.Surgery.Global.Certificate
import PoincareLib.Geometry.RicciFlow.Surgery.Global.ScheduleData

/-!
Adapted from Mapher `PoincareMT/Definitions/M52GlobalFlow.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M52 repaired global controlled-flow data

The final global certificate is the existing changing-carrier
`GlobalSurgeryFlowCertificate`, linked to the M51 partial schedule. The M43
unified continuation theory is a provider used to construct this certificate;
its branch data is not copied into the global output. The inherited
schedule-agreement field records Definition 15.5's source scale
`rho = delta * r` directly at the certificate boundary.

The certificate's volume-loss field is measured against each event's terminal
left-limit metric, rather than the evolving metric at its arbitrary
preterminal reference time.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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
end PoincareMT
