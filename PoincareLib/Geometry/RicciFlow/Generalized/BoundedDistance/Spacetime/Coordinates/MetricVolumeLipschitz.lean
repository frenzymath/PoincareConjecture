import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Spacetime.Coordinates.MetricVolumeCalibration

/-!
# Volume of a Lipschitz image for the actual Riemannian metrics

The same Euclidean calibration on both carriers turns the Hausdorff
image inequality into an inequality for M07 volume. Source: Morgan--Tian
Theorem 5.6, pp. 85-87; M28 derivation 127.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle NNReal ENNReal

universe u v

namespace PoincareMT.M28

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] [T3Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

/-- An extended-distance bound controls the volume of every image set,
including empty sets and infinite measures. Source: Theorem 5.6,
pp. 85-87; M28 derivation 127. -/
theorem volumeMeasure_image_le_of_edist_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) (C : ℝ≥0)
    (hdist : ∀ x y, h.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y)
    (A : Set M) :
    h.volumeMeasure (f '' A) ≤ (C : ℝ≥0∞) ^ n * g.volumeMeasure A := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  have hLip : LipschitzWith C f := by
    intro x y
    change h.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y
    exact hdist x y
  have hmeasure := hLip.hausdorffMeasure_image_le (Nat.cast_nonneg n) A
  rw [ENNReal.rpow_natCast] at hmeasure
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  change (euclideanVolumeCalibration n • Measure.hausdorffMeasure (n : ℝ)) (f '' A) ≤
    (C : ℝ≥0∞) ^ n *
      (euclideanVolumeCalibration n • Measure.hausdorffMeasure (n : ℝ)) A
  simp only [Measure.smul_apply, smul_eq_mul]
  calc
    _ ≤ euclideanVolumeCalibration n *
        ((C : ℝ≥0∞) ^ n * Measure.hausdorffMeasure (n : ℝ) A) :=
      mul_le_mul_right hmeasure _
    _ = _ := by ac_rfl

end PoincareMT.M28
