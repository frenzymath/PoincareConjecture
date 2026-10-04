import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.PoincareInputs
import PoincareLib.Geometry.RicciFlow.Extinction.Global.InitialClass

/-!
# M71 continuation from the Poincare input producer

The initial class and all event comparison inputs are produced before the
existing finite-cover application. Each target uses the literal M56 path,
one M59 output, and the same comparison providers. Source: Morgan--Tian
Proposition 15.12 and Theorem 18.1, pp. 365 and 431--432.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-- Construct M71's finite continuation service from M02/M53/M57 and the
actual M56 Poincare ancestry with the same flow's strict comparison bounds.
No initial class or event input is assumed. -/
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

/-- The scalar clock used by M67 is a projection of pinching on the same
global flow. Only times in the actual domain are asserted. Source:
Morgan--Tian Theorem 15.9 and its use in Theorem 18.1, pp. 363--364, 432. -/
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

/-
Natural-language theorem: on the actual M52 flow of a compact simply connected
initial manifold, raw M38 topology, the M02/M53/M54/M55/M56/M57 services, one
M59 output and its M58/M61/M65/M66 width services construct the complete
input of M71. Ancestry, one initial metric/class, event geometry, point paths
and target covers are all produced on this flow. Its actual M40 provider,
realization and strict event bounds are supplied by the comparison calibration.
The absolute scalar bound is projected from this same global flow's pinching.

Source: Morgan--Tian Proposition 15.12, Definition 18.2 and the Poincare branch
of Theorem 18.1, pp. 365, 419--420 and 431--432. This is checked predecessor
composition; the extinction theorem itself remains the M71 obligation.
-/
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

end PoincareMT
