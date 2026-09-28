import PoincareConjecture.Proofs.M57.PoincareInputs
import PoincareConjecture.Proofs.M71.InitialClass










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




theorem m71ContinuationFromPoincareAncestry
    (P02 : RepairedClosedTopologyProvider.{u})
    (G53 : RepairedSphereSeparationTheory.{u})
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow)
    (P : M56PoincareAncestryData D.flow L)
    (hM61 : M61WidthTheory.{u} (Classical.choose hM59).quotient)
    (hM64 : M64ComparisonTheory.{u})
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM57 : RepairedTransportTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {K : RepairedComparisonMapData D}
    (C : RepairedComparisonHomotopyData D K)
    (hC : RepairedComparisonProviderRealization G40 D C)
    (hcomparison : M67EventComparisonBounds D.flow Set.univ)
    (hscalar : M67ScalarLowerBound D.flow Set.univ) :
    Nonempty (M71FiniteContinuationService D P.witness P.ancestry) := by
  obtain ⟨inputs⟩ := m57PoincareInputsFromTheories hM57 P02 G53 D L P K C
  exact m71ContinuationFromInitialTopology P02 hM59 D L P hM61 hM64 hM65
    hM58 hM66 hM57 G40 C hC hcomparison hscalar inputs




theorem m71ScalarLowerBoundFromGlobalFlow
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    M67ScalarLowerBound G.certificate.flow Set.univ := by
  intro t _ ht x
  exact (G.certificate.pinched t ht).2.1 x (Set.mem_univ x)














theorem m71GlobalInputFromTheories
    (P02 : RepairedClosedTopologyProvider.{u})
    (G53 : RepairedSphereSeparationTheory.{u})
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    (G56 : RepairedAncestryTheory.{u})
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (hM61 : M61WidthTheory.{u} (Classical.choose hM59).quotient)
    (hM64 : M64ComparisonTheory.{u})
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM57 : RepairedTransportTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    {K : RepairedComparisonMapData (m52CoreFlowData G)}
    (C : RepairedComparisonHomotopyData (m52CoreFlowData G) K)
    (hC : RepairedComparisonProviderRealization G40 (m52CoreFlowData G) C)
    (hcomparison : M67EventComparisonBounds G.certificate.flow Set.univ) :
    Nonempty (M71GlobalExtinctionInput N G) := by
  obtain ⟨P, _hP⟩ := m56PoincareAncestryFromTheories G56 G54 G55 G L
  obtain ⟨Q⟩ := m71ContinuationFromPoincareAncestry P02 G53 hM59
    (m52CoreFlowData G) L P hM61 hM64 hM65 hM58 hM66 hM57 G40 C hC
    hcomparison (m71ScalarLowerBoundFromGlobalFlow G)
  exact ⟨m71GlobalInputFromPoincareAncestry G L P Q⟩

end PoincareConjecture
