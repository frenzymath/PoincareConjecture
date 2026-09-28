import PoincareConjecture.Statements.M69
















set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure M70NegativeProfileInput
    {g₀ : StandardInitialMetric}
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
    (C69 : M69FinitePieceConclusion L I HX) where

  B : Set.Icc I.T₁ I.T₂
  profile_negative :
    m68Profile (M69FinitePieceInput.profile L I HX) B.1 < 0

  path_nonempty : Nonempty (D.flow.slice B.1).carrier

structure M70NegativeProfileConclusion
    {g₀ : StandardInitialMetric}
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
    {X : M67ChangingWidthPath D W P K C H B A q hM61 hM65}
    {L : M69ClassLedger P B X}
    {I : M69FinitePieceInput X L}
    {HX : M67Conclusion X}
    {C69 : M69FinitePieceConclusion L I HX}
    (J : M70NegativeProfileInput D W P L I HX C69) where


  contradiction : False

end PoincareConjecture
