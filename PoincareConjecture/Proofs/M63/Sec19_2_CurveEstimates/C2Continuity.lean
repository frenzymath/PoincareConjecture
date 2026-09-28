import PoincareConjecture.Proofs.M63.Adapters
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} (F : RicciFlow n M (Icc a b)) (c : ℝ → ℝ → M)
  (hc : M63C2ShrinkingCurveOn F c (Icc a T))

include hc

theorem c2_speed_pos {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) :
    0 < curveSpeed F c t x :=
  Real.sqrt_pos.mpr ((F.metric t).pos _ _ (hc.immersed t ht x))

theorem c2_unitTangent_norm {t : ℝ} (ht : t ∈ Icc a T) (x : ℝ) :
    (F.metric t).tangentNorm (c x t) (spatialUnitTangent F c t x) = 1 := by
  have hv := (c2_speed_pos F c hc ht x).ne'
  have hinner : (F.metric t).inner (c x t) (spatialUnitTangent F c t x)
      (spatialUnitTangent F c t x) = 1 := by
    simp only [spatialUnitTangent, map_smul, smul_apply, smul_eq_mul]
    rw [← M62.speed_sq F c t x]
    field_simp
  rw [RiemannianMetric.tangentNorm, hinner, Real.sqrt_one]

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

theorem c2_speed_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => curveSpeed F c z.2 z.1) (univ ×ˢ Icc a T) :=
  (c2_metric_pairing_continuousOn F c hc hT _ _
    hc.velocity_continuous hc.velocity_continuous).sqrt

theorem c2_curvatureSquared_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62CurvatureSquared F c z.2 z.1)
      (univ ×ˢ Icc a T) :=
  c2_metric_pairing_continuousOn F c hc hT _ _
    hc.curvature_continuous hc.curvature_continuous

theorem c2_curvature_continuousOn (hT : a < T) :
    ContinuousOn (fun z : ℝ × ℝ => m62Curvature F c z.2 z.1) (univ ×ˢ Icc a T) :=
  (c2_curvatureSquared_continuousOn F c hc hT).sqrt

theorem c2_regularized_continuousOn (hT : a < T) (epsilon : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m62RegularizedCurvature F c epsilon z.2 z.1)
      (univ ×ˢ Icc a T) :=
  ((c2_curvatureSquared_continuousOn F c hc hT).add continuousOn_const).sqrt

theorem c2_length_continuous (hT : a < T) :
    ContinuousOn (m62Length F c) (Icc a T) :=
  (c2_speed_continuousOn F c hc hT).intervalIntegral_prod_left 0 curvePeriod

theorem c2_totalCurvature_continuous (hT : a < T) :
    ContinuousOn (m62TotalCurvature F c) (Icc a T) :=
  ((c2_curvature_continuousOn F c hc hT).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

theorem c2_regularizedTotalCurvature_continuous (hT : a < T) (epsilon : ℝ) :
    ContinuousOn (m62RegularizedTotalCurvature F c epsilon) (Icc a T) :=
  ((c2_regularized_continuousOn F c hc hT epsilon).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

theorem c2_curvatureEnergy_continuous (hT : a < T) :
    ContinuousOn (fun t => ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) (Icc a T) :=
  ((c2_curvatureSquared_continuousOn F c hc hT).mul
    (c2_speed_continuousOn F c hc hT)).intervalIntegral_prod_left 0 curvePeriod

theorem c2_curvatureEnergy_integrable (hT : a < T) :
    IntervalIntegrable (fun t => ∫ x in (0 : ℝ)..curvePeriod,
      m62CurvatureSquared F c t x * curveSpeed F c t x) MeasureTheory.volume a T :=
  ContinuousOn.intervalIntegrable_of_Icc hT.le (c2_curvatureEnergy_continuous F c hc hT)

end PoincareConjecture.M63
