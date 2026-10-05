import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Geometry
import PoincareLib.Geometry.Riemannian.Measure.LocalFinite
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Calibration.Calibration
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Imports.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Measure.Calibration.Calibration

/-!
# Finite volume of the initial cap core

The compact-core volume bound in Morgan-Tian Lemma 12.3, printed pp. 294-295,
follows from M07's local finiteness after identifying its Hausdorff
normalization with the frozen calibrated volume.
-/

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareMT.M34

/-- The unit-ball calibration is the Haar normalization used for intrinsic
Riemannian volume (Morgan-Tian Lemma 12.3, pp. 294-295). -/
theorem volumeCalibration_eq_haarFactor (n : ℕ) :
    euclideanVolumeCalibration n =
      (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) : ℝ≥0∞) := by
  let H : Measure (EuclideanSpace ℝ (Fin n)) := Measure.hausdorffMeasure (n : ℝ)
  let : Measure.IsAddHaarMeasure H := M10.euclideanHausdorff_isAddHaarMeasure n
  have hhaar := Measure.isAddLeftInvariant_eq_smul volume H
  have hball := congrArg
    (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ (Metric.ball 0 1)) hhaar
  unfold euclideanVolumeCalibration
  rw [hball]
  exact ENNReal.mul_div_cancel_right (M10.euclideanHausdorff_unitBall_pos n).ne'
    (M10.euclideanHausdorff_unitBall_lt_top n).ne

/-- The two project volume APIs use the same metric and normalization;
this bridge is used for Lemma 12.3's compact-core bound, pp. 294-295. -/
theorem calibratedVolume_eq_volumeMeasure {n : ℕ} {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric n M) :
    calibratedMetricVolume g = g.volumeMeasure := by
  unfold calibratedMetricVolume RiemannianMetric.volumeMeasure
    Measure.euclideanHausdorffMeasure
  rw [volumeCalibration_eq_haarFactor]
  rfl

/-- Every standard initial metric has a finite positive upper bound for
its actual compact-core volume (Morgan-Tian Lemma 12.3, pp. 294-295). -/
theorem exists_core_volume_bound (g₀ : StandardInitialMetric) :
    ∃ C : ℝ, 0 < C ∧
      calibratedMetricVolume g₀.metric g₀.cylindrical_end.closed_core ≤
        ENNReal.ofReal C := by
  have hfinite : calibratedMetricVolume g₀.metric g₀.cylindrical_end.closed_core < ⊤ := by
    rw [calibratedVolume_eq_volumeMeasure]
    exact g₀.metric.volumeMeasure_lt_top_of_isCompact g₀.cylindrical_end.core_compact
  let V := calibratedMetricVolume g₀.metric g₀.cylindrical_end.closed_core
  refine ⟨V.toReal + 1, add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one, ?_⟩
  calc
    V = ENNReal.ofReal V.toReal := (ENNReal.ofReal_toReal hfinite.ne).symm
    _ ≤ ENNReal.ofReal (V.toReal + 1) :=
      ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)

end PoincareMT.M34
