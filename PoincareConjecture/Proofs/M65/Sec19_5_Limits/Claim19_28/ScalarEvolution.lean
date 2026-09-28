import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Claim19_28.CoordinateEvolution










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



theorem m65Slope_joint_contDiffOn (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Ioo a b) := by
  let := P.charts.chartedSpace
  have hB : ContMDiff (𝓡 (n + 1)) (𝓡 (n + 1)).tangent ∞
      (T% P.charts.circleUnit) := (M62.circleProduct_identities P).circle_unit_smooth
  exact M62.metric_pairing_contDiffOn P.flow c hc.joint_smooth _ _
    (M62.unitTangent_joint_contMDiff P.flow c hc)
    (hB.comp_contMDiffOn hc.joint_smooth)



theorem m65Slope_arcSecond_eq (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    m62ArcSecondDerivative P.flow c t (m62Slope P c t) x =
      deriv (deriv (m62Slope P c t)) x / curveSpeed P.flow c t x ^ 2 -
        deriv (curveSpeed P.flow c t) x * deriv (m62Slope P c t) x /
          curveSpeed P.flow c t x ^ 3 := by
  have hu : ContDiff ℝ ∞ (m62Slope P c t) :=
    (m65Slope_joint_contDiffOn P c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have hdu : HasDerivAt (deriv (m62Slope P c t)) (deriv (deriv (m62Slope P c t)) x) x :=
    ((hu.contDiffAt.derivWithin (m := ∞) (by simp)).differentiableAt
      (by simp)).hasDerivAt
  have hv := ((M62.speed_contDiff P.flow c hc (Ioo_subset_Icc_self ht)).differentiable
    (by norm_num) x).hasDerivAt
  have hpos := (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne'
  have hprod := (hv.fun_inv hpos).fun_mul hdu
  unfold m62ArcSecondDerivative m62ArcDerivative
  rw [hprod.deriv]
  field_simp
  ring



theorem m65Slope_coordinate_evolution (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    {t : ℝ} (ht : t ∈ Ioo a b) (x : ℝ) :
    HasDerivAt (fun r => m62Slope P c r x)
      (deriv (deriv (m62Slope P c t)) x / curveSpeed P.flow c t x ^ 2 -
        deriv (curveSpeed P.flow c t) x * deriv (m62Slope P c t) x /
          curveSpeed P.flow c t x ^ 3 +
        (m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x) *
          m62Slope P c t x) t := by
  simpa only [m65Slope_arcSecond_eq P c hc ht x] using M62.hasDerivAt_slope P c hc ht x




theorem m65NormalizationCoefficient_product_split
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (t x : ℝ) :
    m62TangentRicci P.flow c t x + m62CurvatureSquared P.flow c t x =
      (F.connection t).ricci (c x t).1
        (P.charts.split (c x t) (spatialUnitTangent P.flow c t x)).1
        (P.charts.split (c x t) (spatialUnitTangent P.flow c t x)).1 +
      (F.metric t).inner (c x t).1
        (P.charts.split (c x t) (m62CurvatureVector P.flow c t x)).1
        (P.charts.split (c x t) (m62CurvatureVector P.flow c t x)).1 +
      ((P.flow.metric t).inner (c x t) (m62CurvatureVector P.flow c t x)
        (P.charts.circleUnit (c x t))) ^ 2 := by
  rw [m62TangentRicci, (M62.circleProduct_identities P).ricci_split]
  have hsplit := m65Projection_inner_self P t (c x t) (m62CurvatureVector P.flow c t x)
  change _ = m62CurvatureSquared P.flow c t x - _ at hsplit
  linarith

end PoincareConjecture
