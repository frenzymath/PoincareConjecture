import PoincareLib.Geometry.RicciFlow.CurveShortening.Slope.Evolution
import PoincareLib.Geometry.RicciFlow.CurveShortening.Regularization.Basic

/-!
# The slope bound and sign-guarded lower inequality

Metric Cauchy-Schwarz supplies the closed-domain absolute bound. The exact
evolution gives the lower estimate precisely where the slope is nonnegative.
Source: MT2007 Claim 19.11, p. 446, with the sign repair in
`reviews/errata/2026-09-14-m62-curve-evolution.md`;
see `references/ricci-flow/mapher/curve-evolution/derivations/2026-09-20-slope-evolution.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold Set
open scoped Manifold ContDiff Bundle

namespace PoincareMT.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

/-- The actual slope satisfies all frozen laws, retaining the nonnegative
slope guard in the lower inequality; MT2007 Claim 19.11, p. 446. -/
theorem slope_laws {F : RicciFlow n M (Set.Icc a b)} {circumference : ℝ}
    (P : CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2) : M62SlopeLaws P c K2 := by
  let := P.charts.chartedSpace
  refine ⟨?_, fun _ ht x => hasDerivAt_slope P c hc ht x, ?_⟩
  · intro t ht x
    let g := P.flow.metric t
    let p := c x t
    let S := spatialUnitTangent P.flow c t x
    let B := P.charts.circleUnit p
    let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hS : ‖S‖ = 1 := by
      rw [norm_eq_sqrt_real_inner]
      exact unitTangent_norm P.flow c hc ht x
    have hB : ‖B‖ = 1 := by
      rw [norm_eq_sqrt_real_inner]
      change Real.sqrt (g.inner p B B) = 1
      rw [(circleProduct_identities P).circle_unit]
      norm_num
    change |inner ℝ S B| ≤ 1
    calc
      _ ≤ ‖S‖ * ‖B‖ := abs_real_inner_le_norm S B
      _ = 1 := by rw [hS, hB, mul_one]
  · intro t ht x hu
    have hS : (P.flow.metric t).tangentNorm (c x t) (spatialUnitTangent P.flow c t x) ≤ 1 :=
      (unitTangent_norm P.flow c hc (Ioo_subset_Icc_self ht) x).le
    have hRic : -K2 ≤ m62TangentRicci P.flow c t x :=
      (abs_le.mp (hBounds.ricci t (Ioo_subset_Icc_self ht) (c x t) _ _ hS hS)).1
    have hq := curvatureSquared_nonneg P.flow c t x
    have hcoef : 0 ≤ m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x + K2 :=
      by linarith
    rw [(hasDerivAt_slope P c hc ht x).deriv]
    nlinarith only [mul_nonneg hcoef hu]

end PoincareMT.M62
