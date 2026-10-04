import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.GeometryImports
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.SourceNames
import PoincareLib.Geometry.Riemannian.Measure.Basic
import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.Calibration
import PoincareLib.Geometry.Riemannian.Homothety.Volume
import PoincareLib.Geometry.RicciFlow.Rescaling.Construction
import PoincareLib.Geometry.RicciFlow.Generalized.BoundedDistance.Tube.OpenGeometry.OpenMetricVolume

/-!
# The two intrinsic volume normalizations

The full-neck volume bound uses M07's normalized Hausdorff measure, while
M13 homothety uses the frozen Euclidean unit-ball calibration. Haar
uniqueness identifies their constants. The resulting equality preserves
the exact positive homothety and literal open-region volume readouts.
See the M28 metric-volume-calibration task derivation.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareMT.M28

/-- The frozen unit-ball ratio is the actual normalized Hausdorff factor. -/
theorem euclideanVolumeCalibration_eq_addHaarScalarFactor (n : ℕ) :
    euclideanVolumeCalibration n =
      (Measure.addHaarScalarFactor
        (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (Measure.hausdorffMeasure (n : ℝ)) : ℝ≥0∞) := by
  let H : Measure (EuclideanSpace ℝ (Fin n)) := Measure.hausdorffMeasure (n : ℝ)
  let : Measure.IsAddHaarMeasure H := M10.euclideanHausdorff_isAddHaarMeasure n
  let c : NNReal := Measure.addHaarScalarFactor volume H
  have hhaar : (volume : Measure (EuclideanSpace ℝ (Fin n))) = c • H :=
    Measure.isAddLeftInvariant_eq_smul volume H
  have hball := congrArg
    (fun μ : Measure (EuclideanSpace ℝ (Fin n)) => μ (Metric.ball 0 1)) hhaar
  unfold euclideanVolumeCalibration
  rw [hball]
  exact ENNReal.mul_div_cancel_right (M10.euclideanHausdorff_unitBall_pos n).ne'
    (M10.euclideanHausdorff_unitBall_lt_top n).ne

section General

variable {n : ℕ} {M : Type u} {N : Type v}
  [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- M07 volume is exactly the frozen calibrated volume of the same metric. -/
theorem volumeMeasure_eq_calibratedMetricVolume (g : RiemannianMetric n M) :
    g.volumeMeasure = calibratedMetricVolume g := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change Measure.euclideanHausdorffMeasure n =
    euclideanVolumeCalibration n • (Measure.hausdorffMeasure (n : ℝ) : Measure M)
  rw [Measure.euclideanHausdorffMeasure_def,
    euclideanVolumeCalibration_eq_addHaarScalarFactor, Measure.coe_nnreal_smul]

variable [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N] [T3Space N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]

/-- Positive metric homothety gives the actual M07 volume of every image set. -/
theorem volumeMeasure_homothety_image (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (Q : ℝ) (hQ : 0 < Q) (hf : MetricHomothety g h f Q) (S : Set M) :
    h.volumeMeasure (f '' S) =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * g.volumeMeasure S := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact M13.homothety_volume_image g h f Q hQ hf S

/-- The same-carrier positive metric rescaling has its exact dimensional volume factor. -/
theorem volumeMeasure_scaleSmoothMetric (g : RiemannianMetric n M)
    (Q : ℝ) (hQ : 0 < Q) (S : Set M) :
    RiemannianMetric.volumeMeasure (M13.scaleSmoothMetric g Q hQ) S =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * g.volumeMeasure S := by
  have h := volumeMeasure_homothety_image g (M13.scaleSmoothMetric g Q hQ)
    (Diffeomorph.refl (𝓡 n) M ∞) Q hQ (M13.identity_metricHomothety g Q hQ) S
  simpa only [Diffeomorph.coe_refl, Set.image_id] using h

end General

section OpenRestriction

variable {M : Type u} [TopologicalSpace M] [T2Space M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Inclusion comap preserves M07 volume for the actual intrinsic open metric. -/
theorem intrinsicOpenMetric_volumeMeasure (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) :
    g.volumeMeasure.comap (Subtype.val : U → M) =
      (intrinsicOpenMetric g U).volumeMeasure := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact intrinsicOpenMetric_calibratedVolume g U

/-- A measurable subset of the open carrier has its literal ambient image volume. -/
theorem intrinsicOpenMetric_volumeMeasure_apply (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {S : Set U} (hS : MeasurableSet S) :
    (intrinsicOpenMetric g U).volumeMeasure S =
      g.volumeMeasure ((Subtype.val : U → M) '' S) := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact intrinsicOpenMetric_calibratedVolume_apply g U hS

/-- Total intrinsic open-carrier volume is the volume of that exact ambient carrier. -/
theorem intrinsicOpenMetric_volumeMeasure_univ (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) :
    (intrinsicOpenMetric g U).volumeMeasure Set.univ = g.volumeMeasure (U : Set M) := by
  have himage : (Subtype.val : U → M) '' (Set.univ : Set U) = (U : Set M) := by
    ext x
    constructor
    · rintro ⟨y, _, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, mem_univ _, rfl⟩
  calc
    _ = g.volumeMeasure ((Subtype.val : U → M) '' (Set.univ : Set U)) :=
      intrinsicOpenMetric_volumeMeasure_apply g U MeasurableSet.univ
    _ = g.volumeMeasure (U : Set M) := congrArg g.volumeMeasure himage

/-- Normalize the ambient metric, then restrict to the same literal open carrier. -/
theorem intrinsicOpenMetric_scaleSmoothMetric_volumeMeasure_univ
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) :
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).volumeMeasure Set.univ =
      ENNReal.ofReal (Real.rpow Q ((3 : ℝ) / 2)) * g.volumeMeasure (U : Set M) := by
  rw [intrinsicOpenMetric_volumeMeasure_univ, volumeMeasure_scaleSmoothMetric]
  norm_num

end OpenRestriction

end PoincareMT.M28
