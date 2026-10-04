import PoincareLib.Geometry.RicciFlow.Extinction.Width.Profile.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.Theory

/-!
# M68 scalar clock and piecewise ODE comparison

Natural-language theorem statement: for an actual M67 changing-component
width path and its Proposition 18.18 conclusion, choose any interval
`[T1,T2]` in the nonnegative time domain and its finite ordered surgery list.
The absolute Hamilton--Ivey clock gives `-6/(1+4*t)`, so on each regular piece
the width satisfies the forward-Dini inequality controlled by
`z' = -2*pi + 3*z/(1+4*t)`.  Restart the integrating-factor comparison after
every surgery using M67's lower-limit and right-continuity clauses, and return
the explicit profile bound on the whole interval.  No continuity across a
surgery time is assumed.

Source: Morgan--Tian Definition 18.23 and Claim 18.26, printed pp. 433--434,
`references/derived/MT2007.txt:21204-21255`; Lemma 2.22 and Proposition 2.23,
`3133-3157`; and the comparison step in Theorem 18.1,
`21142-21162`.  The initial profile uses `T1` in both initial-data factors,
as required by the corrected source reading.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

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

end PoincareMT
