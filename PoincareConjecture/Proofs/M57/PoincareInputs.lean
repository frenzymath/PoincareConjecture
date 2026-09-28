import PoincareConjecture.Proofs.M02
import PoincareConjecture.Proofs.M53
import PoincareConjecture.Proofs.M57

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m57PoincareInputsFromTheories
    (hM57 : RepairedTransportTheory.{u})
    (P02 : RepairedClosedTopologyProvider.{u})
    (G53 : RepairedSphereSeparationTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow)
    (P : M56PoincareAncestryData D.flow L)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K) :
    Nonempty (∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C) := by
  exact ⟨fun T hT x =>
    Classical.choice (hM57.poincare_inputs P02 G53 D L P K C T hT x)⟩

theorem m57PoincareInputsFromMilestones
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (L : RawLocalSurgeryTopologyData D.flow)
    (P : M56PoincareAncestryData D.flow L)
    (K : RepairedComparisonMapData D)
    (C : RepairedComparisonHomotopyData D K) :
    Nonempty (∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C) := by
  refine m57PoincareInputsFromTheories repairedAncestryTransport
    ?_ repairedSphereSeparation D L P K C
  intro M _ _ _ _ _ _ _
  exact closedSimplyConnectedThreeManifoldTopology

end PoincareConjecture
