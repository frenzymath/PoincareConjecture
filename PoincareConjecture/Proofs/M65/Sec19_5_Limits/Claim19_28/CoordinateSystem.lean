import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateState









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



theorem m65ProjectedChartJet_mem_domain
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65ProjectedChartJet P c p (t, x) ∈
      m65ProjectedChartOperatorDomain (a := a) (b := b) p := by
  exact ⟨ht, (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source hx,
    M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x⟩



theorem m65ChartHorizontalCurvature_on_actualJet [T2Space M]
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65ChartHorizontalCurvature F p (m65ProjectedChartJet P c p (t, x)) =
      m65ProjectedCoordinateJet P c p 1 t x := by
  unfold m65ChartHorizontalCurvature
  dsimp only [m65ProjectedChartJet]
  rw [m65ProjectedChartState_spatial_deriv P c hc p ht hx,
    m65ProjectedChartState_spatial_second P c hc p ht hx]
  exact (m65ProjectedCoordinateJet_one_eq P c hc p ht hx).symm



theorem m65ChartNormalization_on_actualJet [T2Space M]
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m65ChartNormalization F p (m65ProjectedChartJet P c p (t, x)) =
      m62TangentRicci P.flow c t x + m62CurvatureSquared P.flow c t x := by
  unfold m65ChartNormalization
  rw [m65ChartHorizontalCurvature_on_actualJet P c hc p ht hx]
  dsimp only [m65ProjectedChartJet]
  rw [m65ProjectedChartState_spatial_deriv P c hc p ht hx]
  dsimp only [m65ProjectedChartState]
  rw [← m65ProjectedCoordinateJet_zero_eq P c hc p (Ioo_subset_Icc_self ht) hx]
  exact (m65NormalizationCoefficient_coordinateJets P c hc p ht hx).symm



theorem m65ProjectedChartState_equation [T2Space M]
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    HasDerivAt (fun r => m65ProjectedChartState P c p (r, x))
      (m65ProjectedChartOperator F p (m65ProjectedChartJet P c p (t, x))) t := by
  have hq := m65ProjectedChart_time_deriv P c hc p ht hx
  have hv := M62.hasDerivAt_speed P.flow c hc ht x
  have hu := m65Slope_coordinate_evolution P c hc ht x
  have hprod := (hasDerivAt_id t).prodMk (hq.prodMk (hv.prodMk hu))
  apply hprod.congr_deriv
  unfold m65ProjectedChartOperator
  rw [m65ChartHorizontalCurvature_on_actualJet P c hc p ht hx,
    m65ChartNormalization_on_actualJet P c hc p ht hx]
  dsimp only [m65ProjectedChartJet]
  rw [m65ProjectedChartState_spatial_deriv P c hc p ht hx,
    m65ProjectedChartState_spatial_second P c hc p ht hx]
  simp only [m65ProjectedChartState, add_comm]

end PoincareConjecture
