import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.ChartCoefficients









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem m65NormalizationCoefficient_coordinateJets
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m62TangentRicci P.flow c t x + m62CurvatureSquared P.flow c t x =
      m65FlowChartRicci F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
        (m65ProjectedCoordinateJet P c p 0 t x) (m65ProjectedCoordinateJet P c p 0 t x) +
      m65FlowChartMetric F p (t, (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1)
        (m65ProjectedCoordinateJet P c p 1 t x) (m65ProjectedCoordinateJet P c p 1 t x) +
      (deriv (m62Slope P c t) x / curveSpeed P.flow c t x) ^ 2 := by
  have hvertical : deriv (m62Slope P c t) x / curveSpeed P.flow c t x =
      (P.flow.metric t).inner (c x t) (m62CurvatureVector P.flow c t x)
        (P.charts.circleUnit (c x t)) := by
    rw [div_eq_iff (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne']
    simpa only [mul_comm] using (m65Slope_hasDerivAt P c hc (Ioo_subset_Icc_self ht) x).deriv
  rw [hvertical]
  change _ = m65FlowChartRicci F p _
    (mfderiv (𝓡 n) (𝓡 n) _ _
      (P.charts.split (c x t) (spatialUnitTangent P.flow c t x)).1)
    (mfderiv (𝓡 n) (𝓡 n) _ _
      (P.charts.split (c x t) (spatialUnitTangent P.flow c t x)).1) +
    m65FlowChartMetric F p _
      (mfderiv (𝓡 n) (𝓡 n) _ _
        (P.charts.split (c x t) (m62CurvatureVector P.flow c t x)).1)
      (mfderiv (𝓡 n) (𝓡 n) _ _
        (P.charts.split (c x t) (m62CurvatureVector P.flow c t x)).1) + _
  rw [m65FlowChartRicci_at_source F p ht hx,
    m65FlowChartMetric_at_source F p t hx]
  exact m65NormalizationCoefficient_product_split P c t x



theorem m65ProjectedCoordinateJet_zero_eq
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Icc a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65ProjectedCoordinateJet P c p 0 t x = (curveSpeed P.flow c t x)⁻¹ •
      deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1) x := by
  rw [(m65ProjectedCoordinates_hasDerivAt P c hc p ht hx).deriv, smul_smul,
    inv_mul_cancel₀ (M62.speed_pos P.flow c hc ht x).ne', one_smul]



theorem m65ProjectedCoordinateJet_one_eq [T2Space M]
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65ProjectedCoordinateJet P c p 1 t x =
      (let q : ℝ → EuclideanSpace ℝ (Fin n) :=
        fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1
       (curveSpeed P.flow c t x ^ 2)⁻¹ •
          (deriv (deriv q) x +
            M04.shiChartChristoffel (F.connection t) (chartAt (EuclideanSpace ℝ (Fin n)) p)
              (q x) (deriv q x) (deriv q x)) -
         (deriv (curveSpeed P.flow c t) x / curveSpeed P.flow c t x ^ 3) • deriv q x) := by
  exact (m65ProjectedChart_time_deriv P c hc p ht hx).unique
    (m65ProjectedChart_evolution P c hc p ht hx)

end PoincareConjecture
