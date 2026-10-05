import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.C2.Continuity
import PoincareLib.Geometry.RicciFlow.Product.Circle.Identities

/-!
# Closed slope continuity for C2 labels

The actual circle slope is continuous and has absolute value at most one
through the C2 initial slice. A separately positive slope also gives
continuity of the corrected ratio. Source: MT2007 Claim 19.11, p. 446,
and MT2015Correction pp. 8-9; see `2026-09-21-c2-continuity.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- The actual slope is jointly continuous on a C2 solution's closed slab.
Claim 19.11, MT2007 p. 446, and correction Lemma 0.4, pp. 7-8. -/
theorem c2_slope_continuousOn (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Icc a T) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.continuous.continuousOn.comp
    hc.continuous (fun _ _ => mem_univ _)
  have hpair := c2_metric_pairing_continuousOn P.flow c hc hT _ _
    hc.velocity_continuous hB
  have hinv := (c2_speed_continuousOn P.flow c hc hT).inv₀
    (fun z hz => (c2_speed_pos P.flow c hc hz.2 z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul] using hinv.mul hpair

/-- Metric Cauchy-Schwarz bounds the actual C2 slope at every included time.
No slope sign is assumed; Claim 19.11, MT2007 p. 446. -/
theorem c2_abs_slope_le_one (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) : |m62Slope P c t x| ≤ 1 := by
  let := P.charts.chartedSpace
  let g := P.flow.metric t
  let p := c x t
  let S := spatialUnitTangent P.flow c t x
  let B := P.charts.circleUnit p
  let : RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hS : ‖S‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    exact c2_unitTangent_norm P.flow c hc ht x
  have hB : ‖B‖ = 1 := by
    rw [norm_eq_sqrt_real_inner]
    change Real.sqrt (g.inner p B B) = 1
    rw [(M62.circleProduct_identities P).circle_unit]
    norm_num
  change |inner ℝ S B| ≤ 1
  calc
    _ ≤ ‖S‖ * ‖B‖ := abs_real_inner_le_norm S B
    _ = 1 := by rw [hS, hB, mul_one]

/-- A separately positive C2 slope gives closed continuity of the actual
regularized quotient. Corrected Lemma 19.14, MT2015Correction pp. 8-9. -/
theorem c2_rampRatio_continuousOn (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) (hu : ∀ t ∈ Icc a T, ∀ x, 0 < m62Slope P c t x) (epsilon : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m63RampRatio P c epsilon z.2 z.1)
      (univ ×ˢ Icc a T) :=
  (c2_regularized_continuousOn P.flow c hc hT epsilon).div
    (c2_slope_continuousOn P c hc hT) (fun z hz => (hu z.2 hz.2 z.1).ne')

end PoincareMT.M63
