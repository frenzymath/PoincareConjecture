import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Path.Theory
import PoincareLib.Geometry.RicciFlow.Extinction.Width.Profile.Theory

/-!
# M69 finite-piece width propagation

Natural-language theorem statement: apply the actual M67 changing-carrier
width conclusion and the M68 scalar-clock profile on one M56 ancestry path
carrying one M57/M59 class ledger and a finite ordered surgery interval.  The
strict delta and height bounds hold at every surgery in the path's [0,T], and
the absolute scalar bound holds on its actual flow slices. The full M61,
M58, M65 and M66 services are passed to M67 at their exact indices. The
M67 service retains the supplied initial metric/class, coherent M59 system,
and explicit path-aware basepoint service when selecting the path and its
conclusion; the M68 service selects the
profile used by the returned witness.  The witness records the initial raw M61
width anchor and preservation of the single transported nonzero class.  The
node has no extinction, empty-slice, connected-sum, or Poincare endpoint
premise.

Source: Morgan--Tian Claims 18.19--18.20 and the finite-piece application of
Proposition 18.18 in the proof of Theorem 18.1,
`references/derived/MT2007.txt:21104-21162` and `21124-21140`.
-/

set_option autoImplicit false

universe u

namespace PoincareMT

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

end PoincareMT
