import PoincareConjecture.Definitions.M69
import PoincareConjecture.Statements.M67
import PoincareConjecture.Statements.M68























set_option autoImplicit false

universe u

namespace PoincareConjecture

def M69FinitePieceStatement : Prop :=
  ∀ {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    (hcomparison : M67EventComparisonBounds D.flow (Set.Icc 0 T))
    (hscalar : M67ScalarLowerBound D.flow (Set.Icc 0 T))
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    (S : M59IdentificationSystem.{u})
    (initial : M67InitialClassData S (P.component (m67InitialTime P)) (D.flow.metric 0))
    {hM61 : M61WidthTheory.{u} S.quotient}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61.toM61RawWidthCore hM64}
    (hM58 : RepairedShortLoopTrivialityTheory.{u})
    (hM66 : M66SmoothTimeTheory hM61.toM61RawWidthCore hM58 hM65)
    (hM67 : M67SurgeryWidthTheory.{u})
    (hM68 : M68ScalarClockStatement.{u}),
    let selected := m69M67Choice W P hcomparison hscalar K C H B A S initial
      hM61 hM65 hM58 hM66 hM67
    let X := selected.1
    let HX := selected.2.estimate
    ∀ (L : M69ClassLedger P B X)
      (I : M69FinitePieceInput X L),
      Nonempty {C : M69FinitePieceConclusion L I HX //
        C.profile = Classical.choice (hM68 X HX (M69FinitePieceInput.profile L I HX))}

end PoincareConjecture
