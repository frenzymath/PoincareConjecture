import PoincareConjecture.Proofs.M62.Sec19_3_CircleProductIdentities
import PoincareConjecture.Statements.M62CurveEvolution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem CircleProductData.ambient_bounds
    {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : CircleProductData F circumference) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    CurveEvolutionAmbientBounds P.flow K0 K1 K2 := by
  let := P.charts.chartedSpace
  have hnorm (t : ℝ) (q : P.charts.Point) (V : TangentSpace (𝓡 (n + 1)) q) :
      (F.metric t).tangentNorm q.1 (P.charts.split q V).1 ≤
        (P.flow.metric t).tangentNorm q V := by
    apply Real.sqrt_le_sqrt
    rw [P.metric_eq]
    have hc : 0 ≤ P.circle.metricOnPoints.inner q.2
        (P.charts.split q V).2 (P.charts.split q V).2 := by
      by_cases hz : (P.charts.split q V).2 = 0
      · simp only [hz, map_zero, le_refl]
      · exact (P.circle.metricOnPoints.pos q.2 _ hz).le
    exact le_add_of_nonneg_right hc
  have hP := circleProduct_identities P
  constructor
  · intro t ht q v hv
    rw [hP.riemann_split]
    exact hBounds.riemann t ht q.1 (fun i => (P.charts.split q (v i)).1)
      (fun i => (hnorm t q (v i)).trans (hv i))
  · intro t ht q v hv
    have heq : v = ![v 0, v 1, v 2] := by
      funext i
      fin_cases i <;> rfl
    rw [heq, hP.ricci_derivative_split]
    apply hBounds.ricci_derivative t ht q.1
    intro i
    fin_cases i
    · exact (hnorm t q (v 0)).trans (hv 0)
    · exact (hnorm t q (v 1)).trans (hv 1)
    · exact (hnorm t q (v 2)).trans (hv 2)
  · intro t ht q V W hV hW
    rw [hP.ricci_split]
    exact hBounds.ricci t ht q.1 _ _ ((hnorm t q V).trans hV) ((hnorm t q W).trans hW)

end PoincareConjecture.M62
