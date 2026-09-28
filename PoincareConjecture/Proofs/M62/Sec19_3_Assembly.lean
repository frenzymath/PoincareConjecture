import PoincareConjecture.Proofs.M62.Lemma0_4_CurveTheory
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductFlow
import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductBounds
import PoincareConjecture.Proofs.M62.Sec19_3_CircleSpacetimeParallel
import PoincareConjecture.Proofs.M62.Claim19_11_SlopeLaws

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

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

end PoincareConjecture.M62
