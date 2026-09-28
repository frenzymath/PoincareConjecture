import PoincareConjecture.Definitions.M68
import PoincareConjecture.Statements.M67

set_option autoImplicit false

universe u

namespace PoincareConjecture

def M68ScalarClockStatement : Prop :=
  ∀ {g₀ : StandardInitialMetric}
    {D : RepairedSurgeryFlowData.{u} g₀}
    {W : RepairedEventChildWitness D.flow}
    {T : ℝ} {P : RepairedComponentPath D.flow T W}
    {K : RepairedComparisonMapData D}
    {C : RepairedComparisonHomotopyData D K}
    {H : RepairedAncestryTransportInput D W P K C}
    {B : M59HigherBasepointTransportService}
    {A : RepairedAncestryTransportData D W P K C H B}
    {q : M59SphereQuotient}
    {hM61 : M61RawWidthCore.{u}}
    {hM64 : M64ComparisonTheory.{u}}
    {hM65 : M65DeformationTheory hM61 hM64}
    (X : M67ChangingWidthPath D W P K C H B A q hM61 hM65)
    (HX : M67Conclusion X)
    (I : M68ProfileInput X HX),
    Nonempty (M68ProfileConclusion I)

end PoincareConjecture
