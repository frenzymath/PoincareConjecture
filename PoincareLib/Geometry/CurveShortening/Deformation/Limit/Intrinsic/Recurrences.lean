import PoincareLib.Geometry.CurveShortening.Deformation.Limit.Projection.Connection
import PoincareLib.Geometry.CurveShortening.Deformation.Limit.Intrinsic.Fields

/-!
# Spatial recurrences of the actual horizontal and vertical jets

Morgan--Tian Claim 19.28, printed p. 460. Projection of the actual
pullback connection and parallelness of the circle frame give the
two recurrences used in the coordinate compactness induction.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option backward.isDefEq.respectTransparency false

open Set Bundle
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- The horizontal actual jets satisfy the genuine base covariant
recurrence; Claim 19.28, printed p. 460. -/
theorem m65ProjectedTangentJet_pullback (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (hreg : M63IntrinsicRegularityOn P.flow c (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    rampHorizontalCovariantDerivative (F.connection t) (fun y => (c y t).1)
      (fun y => (P.charts.split (c y t) (m65IntrinsicTangentJet P.flow c i t y)).1) x =
      curveSpeed P.flow c t x •
        (P.charts.split (c x t) (m65IntrinsicTangentJet P.flow c (i + 1) t x)).1 := by
  have hproj := m65Projection_pullback P t
    (m65IntrinsicTangentJet_spatial_mdiff c hc hreg ht i x)
  rw [m65IntrinsicTangentJet_pullback c hc (Ioo_subset_Icc_self ht),
    map_smul, Prod.smul_fst] at hproj
  exact hproj.symm

/-- Every actual vertical jet differentiates to speed times the next
vertical jet, since the fixed circle frame is parallel; Claim 19.28,
printed p. 460. -/
theorem m65VerticalTangentJet_hasDerivAt (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M62ShrinkingCurve P.flow c)
    (hreg : M63IntrinsicRegularityOn P.flow c (Icc a b))
    {t : ℝ} (ht : t ∈ Ioo a b) (i : ℕ) (x : ℝ) :
    HasDerivAt (fun y => (P.flow.metric t).inner (c y t)
      (m65IntrinsicTangentJet P.flow c i t y) (P.charts.circleUnit (c y t)))
      (curveSpeed P.flow c t x * (P.flow.metric t).inner (c x t)
        (m65IntrinsicTangentJet P.flow c (i + 1) t x) (P.charts.circleUnit (c x t))) x := by
  let := P.charts.chartedSpace
  have hP := M62.circleProduct_identities P
  have hcurve : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) (fun y => c y t) x :=
    (hc.spatial_regular t (Ioo_subset_Icc_self ht) x).mdifferentiableAt (by norm_num)
  have hfield : MDifferentiableAt (𝓡 (n + 1)) (𝓡 (n + 1)).tangent
      (T% P.charts.circleUnit) (c x t) :=
    (hP.circle_unit_smooth (c x t)).mdifferentiableAt (by simp)
  have hparallel : rampHorizontalCovariantDerivative (P.flow.connection t)
      (fun y => c y t) (fun y => P.charts.circleUnit (c y t)) x = 0 := by
    rw [M62.pullback_ambient_field (P.flow.connection t) hcurve
      P.charts.circleUnit hfield]
    exact hP.circle_parallel t (c x t) _
  have hp := M62.hasDerivAt_metric_pairing (P.flow.connection t) hcurve
    (m65IntrinsicTangentJet_spatial_mdiff c hc hreg ht i x) (hfield.comp x hcurve)
  apply hp.congr_deriv
  rw [hparallel, m65IntrinsicTangentJet_pullback c hc (Ioo_subset_Icc_self ht)]
  simp only [map_zero, add_zero, map_smul, smul_apply, smul_eq_mul]

end PoincareMT
