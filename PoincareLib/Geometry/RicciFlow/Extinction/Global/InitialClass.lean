import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.ComponentMetric
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.InitialClassAdapters
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Class.Topology.Providers
import PoincareLib.Geometry.RicciFlow.Extinction.Global.ContinuationInputs

/-!
# The fixed initial class on the actual surgery flow

Apply M02 on M56's one initial component, restrict the actual time-zero
metric, and use one M59 output for both loop identification and basepoint
transport. This construction precedes every target-time choice in M71.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

/-
Natural-language theorem: on a surgery flow with the Poincare ancestry
produced by M56, the M02 topology and M59 identification services construct
one initial width class on the literal fixed initial component. Its metric
is the pullback of the flow metric at zero, its second homotopy group is
trivial, and its third class is nonzero at that component's selected point.
No point equality, component metric, or nonzero class is assumed.

Source: Morgan--Tian Proposition 18.18 and Theorem 18.1, pp. 431--432,
specialized to the simply connected initial manifold; see
`reviews/contracts/2026-09-17-m67-selected-basepoint-round1.md`.
-/
set_option linter.style.haveILetI false in
theorem m71InitialClassFromAncestry
    (P02 : RepairedClosedTopologyProvider.{u})
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (F : SurgeryFlowData.{u}) (L : RawLocalSurgeryTopologyData F)
    (P : M56PoincareAncestryData F L) :
    Nonempty (M67InitialClassData (Classical.choose hM59)
      P.ancestry.initial_component (F.metric 0)) := by
  let C := P.ancestry.initial_component
  letI : SimplyConnectedSpace C.carrier.carrier :=
    P.component_simply_connected 0 F.zero_mem C
  letI : CompactSpace C.carrier.carrier := ⟨C.compact⟩
  obtain ⟨topology⟩ := P02 (M := C.carrier.carrier)
  obtain ⟨metric, hpullback⟩ := m39ComponentMetric C (F.metric 0)
  exact m67InitialClassFromM02AtSelectedPoint (Classical.choose hM59)
    (Classical.choice (m59BasepointTransport_from_M59 hM59))
    C (F.metric 0) metric hpullback topology

/-- Supply the existing M02 theorem while retaining the caller's one M59
output and the actual M56 component and time-zero flow metric. -/
theorem m71InitialClassFromM02M59
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (F : SurgeryFlowData.{u}) (L : RawLocalSurgeryTopologyData F)
    (P : M56PoincareAncestryData F L) :
    Nonempty (M67InitialClassData (Classical.choose hM59)
      P.ancestry.initial_component (F.metric 0)) :=
  m71InitialClassFromAncestry m59ClosedTopologyProvider_from_M02 hM59 F L P

/-- Construct the fixed initial class before assembling target covers on
the same M56 paths. Only the still-separate comparison inputs are supplied;
their strict event bounds are retained on that flow. Neither initial width
data nor an extinction premise is requested. -/
theorem m71ContinuationFromInitialTopology
    (P02 : RepairedClosedTopologyProvider.{u})
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
    (hscalar : M67ScalarLowerBound D.flow Set.univ)
    (inputs : ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C) :
    Nonempty (M71FiniteContinuationService D P.witness P.ancestry) := by
  obtain ⟨initial⟩ := m71InitialClassFromAncestry P02 hM59 D.flow L P
  exact m71ContinuationFromM59 P.ancestry hM59 initial hM61 hM64 hM65 hM58 hM66
    hM57 G40 C hC hcomparison hscalar inputs

end PoincareMT
