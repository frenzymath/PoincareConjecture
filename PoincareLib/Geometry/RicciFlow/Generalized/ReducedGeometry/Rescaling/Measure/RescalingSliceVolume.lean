import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Rescaling.Geometry.RescalingGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Measure.Jacobian

/-!
# Actual slice volume under rescaling

Morgan-Tian Definition 3.40 and Lemma 6.75, pp. 61, 142. The supplied
M13 homothety calculus applies to the actual identified slices. Its
measure pushforward gives the set-integral factor, including the
totalized nonintegrable case through measurable-embedding transport.
-/

set_option autoImplicit false
-- Actual slice aliases unfold across the prescribed equality of times.
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {time : X → ℝ} {I : SpacetimeInterval}
  (hM12 : GeneralizedRicciGaugeTheory.{u} n)
  (hM13 : GeneralizedParabolicRescalingTheory.{u} n)
  (G : GeneralizedLGeometryTransport n X time I) (Q : ℝ) (hQ : 0 < Q) (a : ℝ)

/-- The bare M13 slice diffeomorphism at a supplied equal rescaled time.
Definition 3.40, p. 61, and Lemma 6.75, p. 142. -/
noncomputable def rescalingSliceAt (t t' : ℝ) (ht : t' = parabolicTime Q a t) :
    Diffeomorph (𝓡 n) (𝓡 n) (G.slices t).Point
      ((rescalingTransport hM12 hM13 G Q hQ a).slices t').Point ∞ := by
  subst t'
  exact M13.parabolicSliceIdentification G.spacetime G.slices Q hQ a t

/-- The identified slices retain the actual underlying spacetime point.
Definition 3.40, p. 61. -/
theorem rescalingSliceAt_val (t t' : ℝ) (ht : t' = parabolicTime Q a t)
    (p : (G.slices t).Point) :
    (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht p).val = p.val := by
  subst t'
  exact M13.parabolicSliceIdentification_val G.spacetime G.slices Q hQ a t p

/-- The actual slice identification is a metric homothety with scale Q.
Definition 3.40, p. 61. -/
theorem rescalingSliceAt_metric (t t' : ℝ) (ht : t' = parabolicTime Q a t) :
    MetricHomothety (G.slices t).metricOnPoints
      ((rescalingTransport hM12 hM13 G Q hQ a).slices t').metricOnPoints
      (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht) Q := by
  subst t'
  exact M13.parabolicSliceIdentification_metric G.spacetime G.slices Q hQ a t

/-- Calibrated volume is the Q-to-half-dimension multiple of the actual
slice pushforward, by the supplied M13 calculus. Lemma 6.75, p. 142. -/
theorem rescalingSliceAt_volume_map (t t' : ℝ) (ht : t' = parabolicTime Q a t) :
    calibratedMetricVolume ((rescalingTransport hM12 hM13 G Q hQ a).slices t').metricOnPoints =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) • Measure.map
        (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht)
        (calibratedMetricVolume (G.slices t).metricOnPoints) := by
  exact (hM13.metric_homothety (G.slices t).Point
    ((rescalingTransport hM12 hM13 G Q hQ a).slices t').Point
    (G.slices t).metricOnPoints
    ((rescalingTransport hM12 hM13 G Q hQ a).slices t').metricOnPoints
    (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht) Q hQ
    (rescalingSliceAt_metric hM12 hM13 G Q hQ a t t' ht)).volume_map

/-- Arbitrary real set integrals have the slice volume factor under
the actual diffeomorphism. No extra integrability premise is needed for
this totalized integral identity. Lemma 6.75, p. 142. -/
theorem rescalingSliceAt_setIntegral (t t' : ℝ) (ht : t' = parabolicTime Q a t)
    (S : Set (G.slices t).Point)
    (φ : ((rescalingTransport hM12 hM13 G Q hQ a).slices t').Point → ℝ) :
    (∫ q in (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht) '' S, φ q
      ∂calibratedMetricVolume
        ((rescalingTransport hM12 hM13 G Q hQ a).slices t').metricOnPoints) =
      Real.rpow Q ((n : ℝ) / 2) *
        ∫ p in S, φ (rescalingSliceAt hM12 hM13 G Q hQ a t t' ht p)
          ∂calibratedMetricVolume (G.slices t).metricOnPoints := by
  let f := rescalingSliceAt hM12 hM13 G Q hQ a t t' ht
  have hf : MeasurableEmbedding f := f.toHomeomorph.measurableEmbedding
  rw [rescalingSliceAt_volume_map hM12 hM13 G Q hQ a t t' ht]
  have hpre : f ⁻¹' f '' S = S := preimage_image_eq S hf.injective
  rw [Measure.restrict_smul, integral_smul_measure, hf.restrict_map]
  change (ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2))).toReal •
    (∫ q, φ q ∂Measure.map f
      ((calibratedMetricVolume (G.slices t).metricOnPoints).restrict (f ⁻¹' f '' S))) =
        Real.rpow Q ((n : ℝ) / 2) *
          ∫ p in S, φ (f p) ∂calibratedMetricVolume (G.slices t).metricOnPoints
  rw [hpre, hf.integral_map]
  have hc : (ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2))).toReal =
      Real.rpow Q ((n : ℝ) / 2) := ENNReal.toReal_ofReal (Real.rpow_nonneg hQ.le _)
  rw [hc, smul_eq_mul]

end PoincareMT.M14
