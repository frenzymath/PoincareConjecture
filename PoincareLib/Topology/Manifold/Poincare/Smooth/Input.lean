import PoincareLib.Geometry.RicciFlow.Surgery.Global.SelectedCertificate
import PoincareLib.Topology.Manifold.ConnectedSum.SphereReduction

/-! Adapted from Mapher `PoincareMT/Definitions/M75SmoothPoincare.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`; see
`references/ricci-flow/mapher/endpoint-adapters.md`. -/

/-!
# M75 smooth endpoint composition

The producer boundary contains the actual normalized initial metric, the
changing-carrier flow returned by M52, and the M74 reduction of that flow's
time-zero carrier.  No endpoint proposition or original-to-sphere map is an
input: the endpoint map is the composition constructed by M75.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

structure M75EndpointInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] (N : NormalizedInitialMetric (M := M)) where
  global : RepairedGlobalFlowData N
  reduction : Nonempty (M74ReductionConclusion (global.certificate.flow.slice 0))

end PoincareMT
