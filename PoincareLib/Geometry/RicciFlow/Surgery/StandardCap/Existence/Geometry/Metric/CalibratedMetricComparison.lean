import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Metric.MetricComparisonCompleteness
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic

/-!
# Calibrated volume under an actual metric comparison

The Hausdorff Lipschitz estimate transports calibrated volume between the
explicitly selected Riemannian distances. Multiplication by the common
dimension calibration permits arbitrary sets and infinite measure.
Source: Morgan-Tian Proposition 12.13, pp. 304-306, early-slice comparison;
Mathlib `LipschitzWith.hausdorffMeasure_image_le`.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareMT

/-- The actual Riemannian emetric used by calibrated Hausdorff volume
(Proposition 12.13, pp. 304-306). -/
@[instance_reducible] noncomputable def RiemannianMetric.comparisonEMetric
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] (g : RiemannianMetric n M) : EMetricSpace M :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  EMetricSpace.ofRiemannianMetric (𝓡 n) M

namespace M34

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [MeasurableSpace N]
  [BorelSpace M] [BorelSpace N]

/-- An actual distance bound gives the calibrated image-volume estimate,
including infinite measure and dimension zero (Proposition 12.13, pp. 304-306). -/
theorem calibratedMetricVolume_image_le_of_edist_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) {C : ℝ≥0}
    (hbound : ∀ x y, h.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y)
    (A : Set M) :
    calibratedMetricVolume h (f '' A) ≤
      (C : ℝ≥0∞) ^ n * calibratedMetricVolume g A := by
  let : EMetricSpace M := g.comparisonEMetric
  let : EMetricSpace N := h.comparisonEMetric
  have hLip : LipschitzWith C f := hbound
  have hH := hLip.hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity) A
  rw [ENNReal.rpow_natCast] at hH
  change euclideanVolumeCalibration n * _ ≤
    (C : ℝ≥0∞) ^ n * (euclideanVolumeCalibration n * _)
  calc
    _ ≤ euclideanVolumeCalibration n *
        ((C : ℝ≥0∞) ^ n * _) := mul_le_mul_right hH _
    _ = _ := by ac_rfl

omit [MeasurableSpace M] [BorelSpace M] in
/-- A global tangent-length comparison controls the actual distances, also
between different connected components (Proposition 12.13, pp. 304-306). -/
theorem edist_le_of_tangentNorm_le (g h : RiemannianMetric n M)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x),
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (x y : M) :
    h.edist x y ≤ ENNReal.ofReal C * g.edist x y := by
  by_cases hxy : g.edist x y = ⊤
  · simp [hxy, (ENNReal.ofReal_pos.mpr hC).ne']
  let r : ℝ := (g.edist x y).toReal + 1
  have hr : 0 < r := by dsimp [r]; positivity
  have hy : y ∈ g.ball x r := by
    change g.edist x y < ENNReal.ofReal r
    rw [← ENNReal.ofReal_toReal hxy]
    exact (ENNReal.ofReal_lt_ofReal_iff hr).mpr (by dsimp [r]; linarith)
  have hx : x ∈ g.ball x r := by
    change g.edist x x < ENNReal.ofReal r
    change g.comparisonPseudoEMetric.edist x x < ENNReal.ofReal r
    rw [g.comparisonPseudoEMetric.edist_self]
    exact ENNReal.ofReal_pos.mpr hr
  exact RiemannianMetric.edist_le_mul_edist_of_tangentNorm_le_on_ball
    g h x r C hr hC (fun z _ v => hbound z v) hx hy

/-- The identity-map specialization retains both actual metric instances
(Proposition 12.13, pp. 304-306). -/
theorem calibratedMetricVolume_le_of_tangentNorm_le (g h : RiemannianMetric n M)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x),
      h.tangentNorm x v ≤ C * g.tangentNorm x v) (A : Set M) :
    calibratedMetricVolume h A ≤ ENNReal.ofReal C ^ n * calibratedMetricVolume g A := by
  have hdist := edist_le_of_tangentNorm_le g h hC hbound
  have h := calibratedMetricVolume_image_le_of_edist_le g h id
    (C := Real.toNNReal C) hdist A
  simpa only [image_id, ENNReal.ofNNReal_toNNReal] using h

end M34
end PoincareMT
