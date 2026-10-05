import PoincareLib.Geometry.RicciFlow.Extinction.Width.Contradiction.Data
import PoincareLib.Geometry.RicciFlow.Extinction.Width.FinitePiece.Statement

/-!
# M70 finite-piece contradiction statement

Natural-language theorem statement: on one M56 component path, a concrete M69
width and profile witness cannot reach a time `B` whose M68 profile is negative
while the ambient slice remains nonempty.  The contradiction is exactly
`0 <= W(B) <= profile(B) < 0`; M70 exports no empty slice, extinction time,
connected-sum assembly, or Poincare endpoint.  M71 separately ties this local
contradiction to the actual M52 global flow.

Source: Morgan--Tian Theorem 18.1 comparison, using Claims 18.19--18.20 and
Proposition 18.18, `references/derived/MT2007.txt:21104-21114,21124-21162`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

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

end PoincareMT
