import PoincareLib.Geometry.RicciFlow.CurveShortening.Evolution.Theory
import PoincareLib.Geometry.RicciFlow.Product.Circle.Flow
import PoincareLib.Geometry.RicciFlow.Product.Circle.Bounds
import PoincareLib.Geometry.RicciFlow.Product.Circle.SpacetimeParallel
import PoincareLib.Geometry.RicciFlow.CurveShortening.Slope.Laws

/-!
# Assembly of the corrected curve-evolution construction

The actual ambient bounds and curve theory precede every curve and circle
size. Source: MT2015Correction Lemmas 0.1-0.4, pp. 3-8, and MT2007
Section 19.3 and Claim 19.11, pp. 445-446.
See `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-final-assembly.md`.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- Every positive circle retains the supplied bounds and the actual curve
and slope conclusions; MT2007 Section 19.3 and Claim 19.11, pp. 445-446. -/
theorem nonempty_circleConclusion [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2)
    (circumference : ℝ) (hp : 0 < circumference) :
    Nonempty (M62CircleConclusion F circumference K0 K1 K2) := by
  obtain ⟨P⟩ := nonempty_circleProductData F circumference hp
  let := P.charts.chartedSpace
  obtain ⟨T⟩ := nonempty_curveTheory P.flow
  have hP := P.ambient_bounds hBounds
  exact ⟨{
    product := P
    product_identities := circleProduct_identities P
    bounds := hP
    curve_theory := T
    spacetime_parallel := P.spacetime_parallel T.spacetime
    slope := fun c hc => slope_laws P c hc hP
  }⟩

/-- The three nonnegative constants and actual curve theory are chosen
before all curves and circles; MT2015Correction pp. 3-8 and MT2007 pp. 445-446. -/
theorem nonempty_flowConclusion [T2Space M] [SecondCountableTopology M]
    (F : RicciFlow n M (Set.Icc a b)) (hcompact : IsCompact (Set.univ : Set M)) :
    Nonempty (M62FlowConclusion F) := by
  obtain ⟨K0, K1, K2, hK, hBounds⟩ := exists_ambient_bounds F hcompact
  obtain ⟨T⟩ := nonempty_curveTheory F
  exact ⟨{
    K0 := K0
    K1 := K1
    K2 := K2
    nonnegative := hK
    bounds := hBounds
    curve_theory := T
    circle_products := fun circumference hp => nonempty_circleConclusion F hBounds circumference hp
  }⟩

end PoincareMT.M62
