import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateOperator

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

noncomputable def m65ProjectedChartState (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (p : M) (z : ℝ × ℝ) :
    M65ProjectedChartStateSpace n :=
  (z.1, ((chartAt (EuclideanSpace ℝ (Fin n)) p) (c z.2 z.1).1,
    (curveSpeed P.flow c z.1 z.2, m62Slope P c z.1 z.2)))

noncomputable def m65ProjectedChartJet (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (p : M) (z : ℝ × ℝ) :
    M65ProjectedChartJetSpace n :=
  (m65ProjectedChartState P c p z,
    deriv (fun x => m65ProjectedChartState P c p (z.1, x)) z.2,
    deriv (deriv (fun x => m65ProjectedChartState P c p (z.1, x))) z.2)

theorem m65ProjectedChartState_contDiffAt
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    ContDiffAt ℝ ∞ (m65ProjectedChartState P c p) (t, x) := by
  let := P.charts.chartedSpace
  have hswap : ContDiffAt ℝ ∞ (fun z : ℝ × ℝ => (z.2, z.1)) (t, x) := by fun_prop
  have hnear : univ ×ˢ Ioo a b ∈ 𝓝 (x, t) :=
    (isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, ht⟩
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) (𝓡 (n + 1)) ∞
      (fun z : ℝ × ℝ => c z.2 z.1) (t, x) :=
    (hc.joint_smooth.contMDiffAt hnear).comp (t, x) hswap.contMDiffAt
  have hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (Prod.fst : P.charts.Point → M) :=
    contMDiff_fst.comp P.charts.to_product_smooth
  have hbase := hfst.contMDiffAt.comp (t, x) hcurve
  have hchart : ContMDiffAt (𝓡 n) (𝓡 n) ∞
      (chartAt (EuclideanSpace ℝ (Fin n)) p) (c x t).1 :=
    contMDiffOn_chart.contMDiffAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx)
  have hq := (hchart.comp (t, x) hbase).contDiffAt
  have hv := ((M62.speed_joint_contDiffOn P.flow c hc).contDiffAt hnear).comp
    (t, x) hswap
  have hu := ((m65Slope_joint_contDiffOn P c hc).contDiffAt hnear).comp (t, x) hswap
  exact contDiffAt_fst.prodMk (hq.prodMk (hv.prodMk hu))

theorem m65ProjectedChartState_spatial_deriv
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    deriv (fun y => m65ProjectedChartState P c p (t, y)) x =
      (0, (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1) x,
        (deriv (curveSpeed P.flow c t) x, deriv (m62Slope P c t) x))) := by
  have hq := (m65ProjectedCoordinates_hasDerivAt P c hc p
    (Ioo_subset_Icc_self ht) hx).differentiableAt.hasDerivAt
  have hv := ((M62.speed_contDiff P.flow c hc (Ioo_subset_Icc_self ht)).differentiable
    (by norm_num) x).hasDerivAt
  have hu := (m65Slope_hasDerivAt P c hc
    (Ioo_subset_Icc_self ht) x).differentiableAt.hasDerivAt
  exact ((hasDerivAt_const x t).prodMk (hq.prodMk (hv.prodMk hu))).deriv

theorem m65ProjectedChartState_spatial_second [T2Space M]
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (p : M) {t x : ℝ} (ht : t ∈ Ioo a b)
    (hx : (c x t).1 ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    deriv (deriv (fun y => m65ProjectedChartState P c p (t, y))) x =
      (0, (deriv (deriv (fun y => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c y t).1)) x,
        (deriv (deriv (curveSpeed P.flow c t)) x, deriv (deriv (m62Slope P c t)) x))) := by
  have hq := (m65ProjectedChart_second_hasDerivAt P c hc p ht hx).differentiableAt.hasDerivAt
  have hv : ContDiff ℝ ∞ (curveSpeed P.flow c t) :=
    (M62.speed_joint_contDiffOn P.flow c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hu : ContDiff ℝ ∞ (m62Slope P c t) :=
    (m65Slope_joint_contDiffOn P c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hv' : HasDerivAt (deriv (curveSpeed P.flow c t))
      (deriv (deriv (curveSpeed P.flow c t)) x) x :=
    ((hv.contDiffAt.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hu' : HasDerivAt (deriv (m62Slope P c t))
      (deriv (deriv (m62Slope P c t)) x) x :=
    ((hu.contDiffAt.derivWithin (m := ∞) (by simp)).differentiableAt (by simp)).hasDerivAt
  have hprod := (hasDerivAt_const x (0 : ℝ)).prodMk (hq.prodMk (hv'.prodMk hu'))
  have hbase : Continuous (fun y => (c y t).1) :=
    continuous_fst.comp (hc.spatial_regular t (Ioo_subset_Icc_self ht)).continuous
  have heq : deriv (fun y => m65ProjectedChartState P c p (t, y)) =ᶠ[𝓝 x]
      fun y => (0, (deriv (fun z => (chartAt (EuclideanSpace ℝ (Fin n)) p) (c z t).1) y,
        (deriv (curveSpeed P.flow c t) y, deriv (m62Slope P c t) y))) := by
    filter_upwards [hbase.continuousAt
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds hx)] with y hy
    exact m65ProjectedChartState_spatial_deriv P c hc p ht hy
  exact (hprod.congr_of_eventuallyEq heq).deriv

end PoincareConjecture
