import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Basic
import PoincareConjecture.Proofs.M10.Calibration
import PoincareConjecture.Proofs.M13.Volume
import PoincareConjecture.Proofs.M13.OrdinaryFlow
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.OpenMetricVolume

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M28

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

theorem volumeMeasure_homothety_image (g : RiemannianMetric n M)
    (h : RiemannianMetric n N) (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞)
    (Q : ℝ) (hQ : 0 < Q) (hf : MetricHomothety g h f Q) (S : Set M) :
    h.volumeMeasure (f '' S) =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * g.volumeMeasure S := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact M13.homothety_volume_image g h f Q hQ hf S

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

theorem intrinsicOpenMetric_volumeMeasure (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) :
    g.volumeMeasure.comap (Subtype.val : U → M) =
      (intrinsicOpenMetric g U).volumeMeasure := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact intrinsicOpenMetric_calibratedVolume g U

theorem intrinsicOpenMetric_volumeMeasure_apply (g : RiemannianMetric 3 M)
    (U : TopologicalSpace.Opens M) {S : Set U} (hS : MeasurableSet S) :
    (intrinsicOpenMetric g U).volumeMeasure S =
      g.volumeMeasure ((Subtype.val : U → M) '' S) := by
  rw [volumeMeasure_eq_calibratedMetricVolume, volumeMeasure_eq_calibratedMetricVolume]
  exact intrinsicOpenMetric_calibratedVolume_apply g U hS

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

theorem intrinsicOpenMetric_scaleSmoothMetric_volumeMeasure_univ
    (g : RiemannianMetric 3 M) (U : TopologicalSpace.Opens M)
    (Q : ℝ) (hQ : 0 < Q) :
    (intrinsicOpenMetric (M13.scaleSmoothMetric g Q hQ) U).volumeMeasure Set.univ =
      ENNReal.ofReal (Real.rpow Q ((3 : ℝ) / 2)) * g.volumeMeasure (U : Set M) := by
  rw [intrinsicOpenMetric_volumeMeasure_univ, volumeMeasure_scaleSmoothMetric]
  norm_num

end OpenRestriction

end PoincareConjecture.M28
