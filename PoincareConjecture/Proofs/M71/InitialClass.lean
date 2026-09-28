import PoincareConjecture.Proofs.M39.ComponentMetric
import PoincareConjecture.Proofs.M67.InitialClass
import PoincareConjecture.Proofs.M59.Providers
import PoincareConjecture.Proofs.M71.ContinuationInputs

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

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

theorem m71InitialClassFromM02M59
    (hM59 : M59LoopClassesAndComponentTopologyTheory.{u})
    (F : SurgeryFlowData.{u}) (L : RawLocalSurgeryTopologyData F)
    (P : M56PoincareAncestryData F L) :
    Nonempty (M67InitialClassData (Classical.choose hM59)
      P.ancestry.initial_component (F.metric 0)) :=
  m71InitialClassFromAncestry m59ClosedTopologyProvider_from_M02 hM59 F L P

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

end PoincareConjecture
