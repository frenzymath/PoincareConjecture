import PoincareConjecture.Definitions.M52GlobalFlow
import PoincareConjecture.Definitions.M56Ancestry
import PoincareConjecture.Definitions.M70
import PoincareConjecture.Definitions.M67InitialClass
import PoincareConjecture.Definitions.Ch18.FiniteExtinction

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M71ComponentContinuationData
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    (ancestry : RepairedFiniteAncestryData D.flow W)
    (B : M59HigherBasepointTransportService)
    (T : ℝ) (hT : T ∈ D.flow.time_domain) where
  terminal_point : (D.flow.slice T).carrier
  K : RepairedComparisonMapData D
  C : RepairedComparisonHomotopyData D K
  H : RepairedAncestryTransportInput D W
      (ancestry.path_for T hT terminal_point) K C
  A : RepairedAncestryTransportData D W
      (ancestry.path_for T hT terminal_point) K C H B

abbrev M71ComponentContinuationData.P
    {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {ancestry : RepairedFiniteAncestryData D.flow W}
    {B : M59HigherBasepointTransportService}
    {T : ℝ} {hT : T ∈ D.flow.time_domain}
    (J : M71ComponentContinuationData D W ancestry B T hT) :
    RepairedComponentPath D.flow T W :=
  ancestry.path_for T hT J.terminal_point

structure M71FiniteContinuationService
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    (ancestry : RepairedFiniteAncestryData D.flow W) where
  identification_system : M59IdentificationSystem.{u}
  basepoint_service : M59HigherBasepointTransportService
  initial : M67InitialClassData identification_system ancestry.initial_component
    (D.flow.metric 0)
  hM61 : M61WidthTheory.{u} identification_system.quotient
  hM64 : M64ComparisonTheory.{u}
  hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64
  hM58 : RepairedShortLoopTrivialityTheory.{u}
  hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65
  comparison_bounds : M67EventComparisonBounds D.flow Set.univ
  scalar_lower_bound : M67ScalarLowerBound D.flow Set.univ
  target_cover :
    ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain),
      ∃ n : ℕ,
        ∃ packages : Fin n →
          M71ComponentContinuationData D W ancestry basepoint_service T hT,
          ∀ x : (D.flow.slice T).carrier,
            ∃ i : Fin n,
              x ∈ Set.range
                ((packages i).P.component
                  ⟨T, ⟨D.flow.time_domain_nonnegative hT, le_rfl⟩⟩).inclusion

structure M71GlobalExtinctionInput
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    (N : NormalizedInitialMetric (M := M))
    (G : RepairedGlobalFlowData N) where
  g₀ : StandardInitialMetric
  D : RepairedSurgeryFlowData.{u} g₀
  flow_eq : D.flow = G.certificate.flow
  W : RepairedEventChildWitness D.flow
  ancestry : RepairedFiniteAncestryData D.flow W
  initial_connected : IsConnected (Set.univ : Set M)
  initial_group : ∀ x : (D.flow.slice 0).carrier,
    IsFiniteFreeProductCyclic (FundamentalGroup (D.flow.slice 0).carrier x)
  continuation : M71FiniteContinuationService D W ancestry

end PoincareConjecture
