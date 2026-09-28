import PoincareConjecture.Proofs.M71
import PoincareConjecture.Proofs.M71.ComparisonProviders
import PoincareConjecture.Proofs.M71.PoincareInputs










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture




















theorem m71ExtinctionFromCalibratedTheories
    (A25 : RepairedNeckCapTopologyTheory.{u})
    (G38 : RawLocalSurgeryTopologyTheory.{u})
    (G39 : RepairedComparisonMapTheory.{u})
    (G40 : RepairedComparisonHomotopyTheory.{u})
    (P02 : RepairedClosedTopologyProvider.{u})
    (G52 : RepairedGlobalFlowTheory.{u})
    (B28 : RepairedBoundedDistanceTheory.{u})
    (E34 : RepairedStandardCapExistenceTheory)
    (U35 : RepairedStandardCapUniquenessTheory)
    (S36 : RepairedMetricSurgeryTheory.{u})
    (P44 : RepairedCapPersistenceTheory.{u})
    (L15 : GeneralizedNoncollapsingConclusion.{u} 3)
    (U43 : RepairedUnifiedContinuationTheory.{u})
    (S45 : RepairedControlledSchedulesTheory.{u})
    (N46 : RepairedNoncollapseInductionTheory.{u})
    (C47 : RepairedCanonicalInductionTheory.{u})
    (E48 : RepairedEpochExtensionTheory.{u})
    (P48 : M48Predecessors.{u})
    (V49 : RepairedVolumeLossTheory.{u})
    (F50 : RepairedFinitePrefixTheory.{u})
    (G51 : RepairedGlobalScheduleTheory.{u})
    (G53 : RepairedSphereSeparationTheory.{u})
    (G54 : RepairedGroupEffectsTheory.{u})
    (G55 : RepairedChildComponentsTheory.{u})
    (G56 : RepairedAncestryTheory.{u})
    (hM57 : RepairedTransportTheory.{u})
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (hM61 : M61WidthTheory.{u} (Classical.choose hM59).quotient)
    (hM64 : M64ComparisonTheory.{u})
    (hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64)
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM67 : M67SurgeryWidthTheory.{u})
    (hM68 : M68ScalarClockStatement.{u})
    (hM69 : M69FinitePieceStatement.{u})
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M] [SimplyConnectedSpace M]
    (N : NormalizedInitialMetric (M := M))
    (hprojective : NoTrivialNormalProjectivePlane (M := M)) :
    ∃ G : RepairedGlobalFlowData N,
      ∃ _L : RawLocalSurgeryTopologyData G.certificate.flow,
        Nonempty (FiniteExtinctionConclusion G.certificate.flow) := by
  obtain ⟨_K0, _S, start⟩ :=
    m71GlobalFlowWithComparisons A25 G38 G39 G40 P02 G52 B28 E34 U35 S36 P44
      L15 U43 S45 N46 C47 E48 P48 V49 F50 G51
  obtain ⟨G, L, _K, C, _hK0, _hS, _hdelta, _hK, hC, hcomparison, _hbounds⟩ :=
    start N hprojective
  obtain ⟨input⟩ :=
    m71GlobalInputFromTheories P02 G53 G54 G55 G56 hM59 hM61 hM64 hM65
      hM58 hM66 hM57 G40 G L C hC hcomparison
  exact ⟨G, L, m71GlobalFiniteExtinction N G input hM67 hM68 hM69⟩

end PoincareConjecture
