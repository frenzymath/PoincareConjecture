import PoincareConjecture.Definitions.M75SmoothPoincare
import PoincareConjecture.Proofs.M71.TerminalEvent
import PoincareConjecture.Proofs.M72.Providers
import PoincareConjecture.Proofs.M74.Providers










set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

theorem m75EndpointInputFromExtinction
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (E : FiniteExtinctionConclusion G.certificate.flow) :
    ∃ I : M75EndpointInput N, I.global = G := by
  let I := m72ReconstructionInputFromRaw G L E isConnected_univ
  exact ⟨{ global := G, reduction := m74Reduction_from_M72_M73 I }, rfl⟩




theorem m75EndpointInputFromEmpty
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (T : ℝ) (hT : T ∈ G.certificate.flow.time_domain)
    (hempty : IsEmpty (G.certificate.flow.slice T).carrier) :
    ∃ I : M75EndpointInput N, I.global = G := by
  obtain ⟨E, _hET, _hearlier⟩ := m71FirstEmptySurgery G.certificate T hT hempty
  exact m75EndpointInputFromExtinction G L E

end PoincareConjecture
