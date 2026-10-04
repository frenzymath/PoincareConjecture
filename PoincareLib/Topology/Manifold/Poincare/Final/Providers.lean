import PoincareLib.Geometry.CurveShortening.Deformation.Main
import PoincareLib.Geometry.Riemannian.Normalization.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.Noncollapse
import PoincareLib.Topology.Manifold.NeckCap
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Predecessors.BoundedDistance
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.RegularLimit
import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Main
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Existence
import PoincareLib.Topology.Manifold.Surgery.Event.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Extension.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Existence
import PoincareLib.Geometry.RicciFlow.Surgery.Continuation.Unified
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Main
import PoincareLib.Geometry.RicciFlow.Surgery.CapPersistence.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.ControlledSchedules.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.Noncollapse.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Providers
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.VolumeLoss
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.FinitePrefix
import PoincareLib.Geometry.RicciFlow.Surgery.GlobalSchedule.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Global.Existence
import PoincareLib.Topology.Manifold.EmbeddedSphere.Separation
import PoincareLib.Topology.Manifold.Surgery.GroupEffects.Main
import PoincareLib.Topology.Manifold.Surgery.Children.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Finite.Main
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Main
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.Compatibility.ShortLoops
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.Providers
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Main
import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.Width
import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Propagation
import PoincareLib.Geometry.RicciFlow.Extinction.Global.Assembly
import PoincareLib.Topology.Manifold.Poincare.Smooth
import PoincareLib.Topology.Manifold.Poincare.Smooth.Providers
import PoincareLib.Topology.Manifold.Smoothing.Compatible
import PoincareLib.Topology.Manifold.Poincare.Smoothing.Topology
import PoincareLib.Topology.Manifold.Poincare.Transport
import PoincareLib.Topology.Manifold.Poincare.Topological
import PoincareLib.Topology.Manifold.Poincare.Assembly
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Exclusion

/-!
# Actual milestone suppliers for the two endpoints

All services are supplied inside checked theorem proofs. The original
manifold, chosen normalized metric, calibrated flow, event topology and
extinction conclusion stay fixed through reconstruction. No endpoint service,
sphere identification or projective-plane exclusion is an input.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT

/-- On each compact Hausdorff second-countable simply connected smooth
three-manifold with its Borel measurable structure, the actual milestones
supply a normalized metric, one global flow and the reduction of that flow's
initial slice required by M75. M01 supplies the metric; M02/M83 exclude a
two-sided projective plane; M71 supplies extinction on the calibrated flow;
M72--M74 reconstruct and reduce the same flow through the checked M75 adapter.

Sources: Morgan--Tian Theorem 0.3 footnote 2, p. xii; Theorem 15.9 and
Corollary 15.10, pp. 363-364; Theorem 18.1, p. 415; Corollary 15.4(2),
pp. 358-359. This is checked assembly with no additional admission. -/
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

/-- The actual M75 input producer proves smooth Poincare. M76--M79 then
transport that result through a compatible smooth model of each original
topological manifold; M80 packages both unchanged endpoint propositions.
Sources: Morgan--Tian Corollary 0.2(a), with Hamilton Theorem 2(1), p. 64,
and Cairns Theorem III, p. 797, through M76's reviewed smoothing contract.
All inputs are supplied milestone results; this theorem has no new admission. -/
theorem m90EndpointPackageFromMilestones : Nonempty (M80EndpointConclusion.{u}) := by
  have hSmooth : SmoothPoincare.{u} := m75SmoothPoincare m90SmoothEndpointInputs
  have hTopological : TopologicalPoincare.{u} :=
    m79TopologicalPoincare m76CompatibleSmoothing m77TransportTopologicalHypotheses
      hSmooth m78EndpointTransport
  exact m80EndpointAssembly hSmooth hTopological

end PoincareMT
