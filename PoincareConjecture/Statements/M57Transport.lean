import PoincareConjecture.Definitions.M57Transport
import PoincareConjecture.Statements.M40ComparisonHomotopy
import PoincareConjecture.Statements.M53SphereSeparation
import PoincareConjecture.Statements.M56Ancestry










set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def RepairedComparisonProviderRealization
    (G40 : RepairedComparisonHomotopyTheory.{u})
    {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    {K : RepairedComparisonMapData D}
    (C : RepairedComparisonHomotopyData D K) : Prop :=
  ∃ P : RepairedClosedTopologyProvider.{u},
    ∃ G39 : RepairedComparisonMapTheory.{u},
      let epsilon₀ := Classical.choose (G40.homotopy P G39)
      let hprovider := Classical.choose_spec (G40.homotopy P G39)
      ∃ hsmall : 2 * D.flow.parameters.epsilon ≤ epsilon₀,
        ∃ hK : RepairedComparisonMapProviderRealization G39 D K,
          C = Classical.choice (hprovider.2 D hsmall K hK)








































structure RepairedTransportTheory : Prop where
  poincare_inputs :
    (P02 : RepairedClosedTopologyProvider.{u}) →
    (G53 : RepairedSphereSeparationTheory.{u}) →
    ∀ {g₀ : StandardInitialMetric}
      (D : RepairedSurgeryFlowData.{u} g₀)
      (L : RawLocalSurgeryTopologyData D.flow)
      (P : M56PoincareAncestryData D.flow L)
      (K : RepairedComparisonMapData D)
      (C : RepairedComparisonHomotopyData D K)
      (T : ℝ) (hT : T ∈ D.flow.time_domain)
      (x : (D.flow.slice T).carrier),
      Nonempty (RepairedAncestryTransportInput D P.witness
        (P.ancestry.path_for T hT x) K C)
  transport : ∀ (B : M59HigherBasepointTransportService.{u}),
    ∀ (G40 : RepairedComparisonHomotopyTheory.{u}),
    ∀ {g₀ : StandardInitialMetric}
      (D : RepairedSurgeryFlowData.{u} g₀)
      (W : RepairedEventChildWitness D.flow)
      (A : RepairedFiniteAncestryData D.flow W)
      {K : RepairedComparisonMapData D}
      (C : RepairedComparisonHomotopyData D K),
      RepairedComparisonProviderRealization G40 D C →
      ∀ (T : ℝ) (hT : T ∈ D.flow.time_domain)
        (x : (D.flow.slice T).carrier),
        (H : RepairedAncestryTransportInput D W
          (A.path_for T hT x) K C) →
        Nonempty (RepairedAncestryTransportData D W
          (A.path_for T hT x) K C H B)

end PoincareConjecture
