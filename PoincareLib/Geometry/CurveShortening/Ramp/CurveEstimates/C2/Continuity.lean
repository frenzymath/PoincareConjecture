import PoincareLib.Geometry.CurveShortening.Ramp.Adapters
import PoincareLib.Geometry.RicciFlow.CurveShortening.Integral.Continuity

/-!
# Closed continuity for the primitive C2 solution record

The actual continuous bundled velocity and curvature fields give continuous
metric quantities and spatial integrals through the C2 initial slice.
The proof uses M62's general continuous pairing and parameter-integral APIs
on the literal restricted flow. Source: correction Lemma 0.4 and Corollary
19.10, pp. 7-8; see `2026-09-21-c2-continuity.md`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
  (hc : M63C2ShrinkingCurveOn F c (Icc a T))

include hc

/-- Immersion gives positive actual speed through the C2 endpoints.
MT2007 Lemma 19.6, p. 441; correction Lemma 0.1, p. 3. -/
theorem c2_speed_pos {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) :
    0 < curveSpeed F c t x :=
  Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t ht x))

/-- The actual normalized tangent of a C2 immersed slice is unit length.
This is pointwise metric normalization; MT2007 Lemma 19.6, p. 441. -/
theorem c2_unitTangent_norm {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) :
    (F.metric t).tangentNorm (c x t) (spatialUnitTangent F c t x) = 1 := by
  have hv := (c2_speed_pos F c hc ht x).ne'
  have hinner : (F.metric t).inner (c x t) (spatialUnitTangent F c t x)
      (spatialUnitTangent F c t x) = 1 := by
    simp only [spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
    rw [← M62.speed_sq F c t x]
    field_simp
  rw [RiemannianMetric.tangentNorm, hinner, Real.sqrt_one]

/-- M62's continuous metric-pairing theorem applies on the literal restricted
slab without a smooth-curve premise. Correction Lemma 0.4, pp. 7-8. -/
theorem c2_metric_pairing_continuousOn (hT : a < T)
    (Y Z : (z : ℝ × ℝ) → TangentSpace (𝓡 n) (c z.1 z.2))
    (hY : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨c z.1 z.2, Y z⟩ : TangentBundle (𝓡 n) M)) (univ ×ˢ Icc a T))
    (hZ : ContinuousOn (fun z : ℝ × ℝ =>
      (⟨c z.1 z.2, Z z⟩ : TangentBundle (𝓡 n) M)) (univ ×ˢ Icc a T)) :
    ContinuousOn (fun z : ℝ × ℝ =>
      (F.metric z.2).inner (c z.1 z.2) (Y z) (Z z)) (univ ×ˢ Icc a T) := by
  exact M62.metric_pairing_continuousOn
    (m63RestrictClosedFlow F a T hc.domain_subset hT) c hc.continuous Y Z hY hZ

/-- Actual speed is continuous through the original C2 initial slice.
Correction Lemma 0.4, pp. 7-8. -/
theorem c2_speed_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 z.1) (univ ×ˢ Icc a T) :=
  (c2_metric_pairing_continuousOn F c hc hT _ _
    hc.velocity_continuous hc.velocity_continuous).sqrt

/-- Squared curvature is jointly continuous on the C2 closed slab.
Correction Lemma 0.4, pp. 7-8. -/
theorem c2_curvatureSquared_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62CurvatureSquared F c z.2 z.1)
      (univ ×ˢ Icc a T) :=
  c2_metric_pairing_continuousOn F c hc hT _ _
    hc.curvature_continuous hc.curvature_continuous

/-- Taking the curvature norm preserves continuity at its zero set.
Correction Lemma 0.4, pp. 7-8. -/
theorem c2_curvature_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62Curvature F c z.2 z.1) (univ ×ˢ Icc a T) :=
  (c2_curvatureSquared_continuousOn F c hc hT).sqrt

/-- Every fixed regularized curvature is continuous on the C2 closed slab.
No sign of epsilon is needed for continuity; correction pp. 6-8. -/
theorem c2_regularized_continuousOn (hT : a < T) (epsilon : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m62RegularizedCurvature F c epsilon z.2 z.1)
      (univ ×ˢ Icc a T) :=
  ((c2_curvatureSquared_continuousOn F c hc hT).add continuousOn_const).sqrt

/-- Actual length is continuous on the entire C2 time interval.
Correction Lemma 0.4 and Corollary 19.10, pp. 7-8. -/
theorem c2_length_continuous (hT : a < T) :
    ContinuousOn (m62Length F c) (Icc a T) :=
  (c2_speed_continuousOn F c hc hT).intervalIntegral_prod_left 0 curvePeriod

/-- Actual total curvature is continuous through both C2 time endpoints.
Correction Lemma 0.4, pp. 7-8. -/
theorem c2_totalCurvature_continuous (hT : a < T) :
    ContinuousOn (m62TotalCurvature F c) (Icc a T) :=
  ((c2_curvature_continuousOn F c hc hT).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

/-- Regularized total curvature is continuous for each fixed real epsilon.
Correction Lemma 0.4, pp. 7-8. -/
theorem c2_regularizedTotalCurvature_continuous (hT : a < T) (epsilon : ℝ) :
    ContinuousOn (m62RegularizedTotalCurvature F c epsilon) (Icc a T) :=
  ((c2_regularized_continuousOn F c hc hT epsilon).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

/-- The actual spatial curvature-energy integral is continuous in C2 time.
Correction Lemma 0.4 and the length identity, pp. 7-8. -/
theorem c2_curvatureEnergy_continuous (hT : a < T) :
    ContinuousOn (fun t => ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) (Icc a T) :=
  ((c2_curvatureSquared_continuousOn F c hc hT).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

/-- Closed continuity supplies integrability of the actual time energy.
This is the integrability field required by M63, correction pp. 7-8. -/
theorem c2_curvatureEnergy_integrable (hT : a < T) :
    IntervalIntegrable (fun t => ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) MeasureTheory.volume a T :=
  ContinuousOn.intervalIntegrable_of_Icc hT.le (c2_curvatureEnergy_continuous F c hc hT)

end PoincareMT.M63
