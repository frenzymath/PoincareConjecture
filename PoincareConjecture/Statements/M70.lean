import PoincareConjecture.Definitions.M70
import PoincareConjecture.Statements.M69

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

def M70FiniteExtinctionStatement : Prop :=
  ∀ {g₀ : StandardInitialMetric}
    (D : RepairedSurgeryFlowData.{u} g₀)
    (W : RepairedEventChildWitness D.flow)
    {T : ℝ} (P : RepairedComponentPath D.flow T W)
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    (L : M69ClassLedger P B X)
    (I : M69FinitePieceInput X L)
    (HX : M67Conclusion X)
    (C69 : M69FinitePieceConclusion L I HX),
    ∀ (J : M70NegativeProfileInput D W P L I HX C69),
    Nonempty (M70NegativeProfileConclusion J)

end PoincareConjecture
