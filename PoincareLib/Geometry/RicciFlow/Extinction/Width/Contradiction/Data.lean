import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Statement

/-!
# M70 component finite-extinction contradiction

M70 isolates the numerical contradiction in the finite-extinction argument.
The width and profile are the concrete M69 outputs on one repaired component
path.  The only extra datum is a time in the M68 interval where the displayed
profile is negative and the ambient slice is still nonempty.  M71 supplies the
separate adapter from the global M52 flow to this local path.

Source: Morgan--Tian Claims 18.19--18.20 and Proposition 18.18 in the proof
of Theorem 18.1, `references/derived/MT2007.txt:21104-21114` and
`21124-21162`.  The local conclusion is only the inequality contradiction;
finite extinction and the terminal vanishing event belong to M71.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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
  /-- The time is chosen from the interval on which M68's profile is defined. -/
  B : Set.Icc I.T₁ I.T₂
  profile_negative :
    m68Profile (M69FinitePieceInput.profile L I HX) B.1 < 0
  /-- The component path still represents a nonempty ambient slice at B. -/
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
  /-- The width is simultaneously nonnegative and bounded above by a
      negative M68 profile value. -/
  contradiction : False

end PoincareMT
