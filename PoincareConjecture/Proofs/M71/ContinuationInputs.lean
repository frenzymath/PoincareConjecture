import PoincareConjecture.Definitions.M71FiniteExtinction
import PoincareConjecture.Proofs.M56.InitialAnchor
import PoincareConjecture.Proofs.M56.Poincare
import PoincareConjecture.Proofs.M59.Providers
import PoincareConjecture.Statements.M57Transport











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

noncomputable def m71ContinuationPackage
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    (ancestry : RepairedFiniteAncestryData D.flow W)
    (B : M59HigherBasepointTransportService.{u})
    (hM57 : RepairedTransportTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {K : RepairedComparisonMapData D} (C : RepairedComparisonHomotopyData D K)
    (hC : RepairedComparisonProviderRealization G40 D C)
    (T : ℝ) (hT : T ∈ D.flow.time_domain) (x : (D.flow.slice T).carrier)
    (H : RepairedAncestryTransportInput D W (ancestry.path_for T hT x) K C) :
    M71ComponentContinuationData D W ancestry B T hT where
  terminal_point := x
  K := K
  C := C
  H := H
  A := Classical.choice (hM57.transport B G40 D W ancestry C hC T hT x H)












theorem m71InitialSliceConnected
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (hM : IsConnected (Set.univ : Set M)) :
    IsConnected (Set.univ : Set (G.certificate.flow.slice 0).carrier) := by
  have himage := hM.image G.certificate.initial_identification
    G.certificate.initial_identification.continuous.continuousOn
  rw [Set.image_univ] at himage
  change IsConnected (Set.range (G.certificate.initial_identification : M → _)) at himage
  have hrange : Set.range (G.certificate.initial_identification : M → _) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro y
    exact G.certificate.initial_identification.surjective y
  rw [hrange] at himage
  exact himage










theorem m71InitialSliceSimplyConnected
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    SimplyConnectedSpace (G.certificate.flow.slice 0).carrier := by
  exact
    (G.certificate.initial_identification.toHomeomorph.symm.toHomotopyEquiv).simplyConnectedSpace


set_option linter.style.haveILetI false in
theorem m71InitialGroupsFromOriginal
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N) :
    ∀ x : (G.certificate.flow.slice 0).carrier,
      IsFiniteFreeProductCyclic
        (FundamentalGroup (G.certificate.flow.slice 0).carrier x) := by
  letI : SimplyConnectedSpace (G.certificate.flow.slice 0).carrier :=
    m71InitialSliceSimplyConnected G
  exact finiteFreeProductCyclic_of_simplyConnected

theorem m71ContinuationFromTransport
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    (ancestry : RepairedFiniteAncestryData D.flow W)
    (S : M59IdentificationSystem.{u}) (B : M59HigherBasepointTransportService.{u})
    (initial : M67InitialClassData S ancestry.initial_component (D.flow.metric 0))
    (hM61 : M61WidthTheory.{u} S.quotient) (hM64 : M64ComparisonTheory.{u})
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM57 : RepairedTransportTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {K : RepairedComparisonMapData D} (C : RepairedComparisonHomotopyData D K)
    (hC : RepairedComparisonProviderRealization G40 D C)
    (hcomparison : M67EventComparisonBounds D.flow Set.univ)
    (hscalar : M67ScalarLowerBound D.flow Set.univ)
    (inputs : ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain) (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D W (ancestry.path_for T hT x) K C) :
    Nonempty (M71FiniteContinuationService D W ancestry) := by
  refine ⟨{
    identification_system := S
    basepoint_service := B
    initial := initial
    hM61 := hM61
    hM64 := hM64
    hM65 := hM65
    hM58 := hM58
    hM66 := hM66
    comparison_bounds := hcomparison
    scalar_lower_bound := hscalar
    target_cover := ?_ }⟩
  intro T hT
  obtain ⟨n, points, hcover⟩ := m56LiteralPathCover ancestry T hT
  exact ⟨n, fun i => m71ContinuationPackage ancestry B hM57 G40 C hC T hT
    (points i) (inputs T hT (points i)), hcover⟩





theorem m71ContinuationFromM59
    {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    (ancestry : RepairedFiniteAncestryData D.flow W)
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (initial : M67InitialClassData (Classical.choose hM59)
      ancestry.initial_component (D.flow.metric 0))
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
    (hscalar : M67ScalarLowerBound D.flow Set.univ)
    (inputs : ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D W
        (ancestry.path_for T hT x) K C) :
    Nonempty (M71FiniteContinuationService D W ancestry) := by
  exact m71ContinuationFromTransport ancestry (Classical.choose hM59)
    (Classical.choice (m59BasepointTransport_from_M59 hM59)) initial hM61 hM64
    hM65 hM58 hM66 hM57 G40 C hC hcomparison hscalar inputs





def m71GlobalInputFromPoincareAncestry
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
    {N : NormalizedInitialMetric (M := M)}
    (G : RepairedGlobalFlowData N)
    (L : RawLocalSurgeryTopologyData G.certificate.flow)
    (P : M56PoincareAncestryData (m52CoreFlowData G).flow L)
    (Q : M71FiniteContinuationService (m52CoreFlowData G) P.witness P.ancestry) :
    M71GlobalExtinctionInput N G where
  g₀ := G.certificate.flow.standard_initial
  D := m52CoreFlowData G
  flow_eq := rfl
  W := P.witness
  ancestry := P.ancestry
  initial_connected := isConnected_univ
  initial_group := m71InitialGroupsFromOriginal G
  continuation := Q

end PoincareConjecture
