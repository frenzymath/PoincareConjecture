import PoincareConjecture.Proofs.M01
import PoincareConjecture.Proofs.M15.Providers
import PoincareConjecture.Proofs.M25
import PoincareConjecture.Proofs.M28
import PoincareConjecture.Proofs.M31
import PoincareConjecture.Proofs.M32.Providers
import PoincareConjecture.Proofs.M33.Providers
import PoincareConjecture.Proofs.M34
import PoincareConjecture.Proofs.M35.Providers
import PoincareConjecture.Proofs.M36
import PoincareConjecture.Proofs.M38
import PoincareConjecture.Proofs.M39
import PoincareConjecture.Proofs.M40
import PoincareConjecture.Proofs.M43
import PoincareConjecture.Proofs.M44
import PoincareConjecture.Proofs.M44.Providers
import PoincareConjecture.Proofs.M45.Providers
import PoincareConjecture.Proofs.M46.Providers
import PoincareConjecture.Proofs.M47.Providers
import PoincareConjecture.Proofs.M48
import PoincareConjecture.Proofs.M49
import PoincareConjecture.Proofs.M50
import PoincareConjecture.Proofs.M51
import PoincareConjecture.Proofs.M52
import PoincareConjecture.Proofs.M53
import PoincareConjecture.Proofs.M54
import PoincareConjecture.Proofs.M55
import PoincareConjecture.Proofs.M56
import PoincareConjecture.Proofs.M57
import PoincareConjecture.Proofs.M58
import PoincareConjecture.Proofs.M59.Providers
import PoincareConjecture.Proofs.M61
import PoincareConjecture.Proofs.M66
import PoincareConjecture.Proofs.M67
import PoincareConjecture.Proofs.M68
import PoincareConjecture.Proofs.M69
import PoincareConjecture.Proofs.M71.Assembly
import PoincareConjecture.Proofs.M75
import PoincareConjecture.Proofs.M75.Providers
import PoincareConjecture.Proofs.M76
import PoincareConjecture.Proofs.M77
import PoincareConjecture.Proofs.M78
import PoincareConjecture.Proofs.M79
import PoincareConjecture.Proofs.M80
import PoincareConjecture.Proofs.M83

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture

theorem m90SmoothEndpointInputs
    (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [T2Space M] [T3Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [CompactSpace M] [SimplyConnectedSpace M] :
    ∃ N : NormalizedInitialMetric (M := M), Nonempty (M75EndpointInput N) := by
  classical
  obtain ⟨N0⟩ := existsNormalizedInitialMetric (M := M)
  let A25 : RepairedNeckCapTopologyTheory.{u} := Classical.choice m25NeckCapTopology
  let P48 : M48Predecessors.{u} :=
    { m11 := generalizedSpacetimeGeometry 3
      m12 := generalizedRicciGaugeGeometry_from_M03_M04_M11 3
      m13 := generalizedParabolicRescaling_from_M12 3
      m31 := m31SingularRegularLimitTheory
      m32 := m32HornSelectionFromMilestones
      m33 := m33BranchContinuationFromMilestones
      m36 := repairedMetricSurgery
      m43 := repairedUnifiedContinuation }
  let hM59 := m59LoopClassesAndComponentTopology_from_predecessors.{u}
  let hM61 := m61Widths (Classical.choose hM59) m60AreaAndFilling_from_predecessors
  let hM64 := m64AnnulusComparison_from_predecessors.{u}
  let hM65 := m65LoopFamilyDeformation hM61.toM61RawWidthCore hM64
  let hM66 := m66SmoothTimeWidthComparison hM61.toM61RawWidthCore
    repairedShortLoopTriviality hM65
  obtain ⟨G, L, ⟨E⟩⟩ :=
    m71ExtinctionFromCalibratedTheories A25 rawLocalSurgeryTopology
      repairedComparisonMap repairedComparisonHomotopy m59ClosedTopologyProvider_from_M02
      repairedGlobalFlow (m28BoundedDistance ⟨ricciFlowCurvatureTheory, ⟨A25⟩⟩)
      repairedStandardCapExistence m35StandardCapUniquenessFromMilestones
      repairedMetricSurgery m44CapPersistenceFromMilestones
      (noncollapsingGeneralizedAndCompact_from_predecessors 3).generalized
      repairedUnifiedContinuation m45ControlledSchedulesTheoryFromMilestones
      m46NoncollapseInductionFromMilestones m47CanonicalInductionFromMilestones
      repairedEpochExtension P48
      repairedVolumeLoss repairedFinitePrefix repairedGlobalSchedule
      repairedSphereSeparation repairedGroupEffects repairedChildComponents repairedFiniteAncestry
      repairedAncestryTransport hM59 hM61 hM64 hM65 repairedShortLoopTriviality hM66
      m67SurgeryWidthTheory m68ScalarClockTheory m69FinitePiecePropagation N0.data
      (m83NoProjectivePlaneFromMilestones (M := M))
  obtain ⟨I, _hI⟩ := m75EndpointInputFromExtinction G L E
  exact ⟨N0.data, ⟨I⟩⟩

theorem m90EndpointPackageFromMilestones : Nonempty (M80EndpointConclusion.{u}) := by
  have hSmooth : SmoothPoincare.{u} := m75SmoothPoincare m90SmoothEndpointInputs
  have hTopological : TopologicalPoincare.{u} :=
    m79TopologicalPoincare m76CompatibleSmoothing m77TransportTopologicalHypotheses
      hSmooth m78EndpointTransport
  exact m80EndpointAssembly hSmooth hTopological

end PoincareConjecture
