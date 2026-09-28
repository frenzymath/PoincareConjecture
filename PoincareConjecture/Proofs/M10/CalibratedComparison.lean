import PoincareConjecture.Proofs.M10.Calibration
import Mathlib.Analysis.InnerProductSpace.NormDet









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]
  {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]

set_option backward.isDefEq.respectTransparency false in

theorem calibratedMetricVolume_image_le_of_normalized_lipschitz
    (g : RiemannianMetric n M) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y)
    {f : EuclideanSpace ℝ (Fin n) → M} {S A : Set (EuclideanSpace ℝ (Fin n))}
    {C : ℝ≥0} (hAS : A ⊆ S)
    (hf :
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      LipschitzOnWith C (f ∘ L.symm) (L '' S)) :
    calibratedMetricVolume g (f '' A) ≤
      (C : ℝ≥0∞) ^ n * ENNReal.ofReal L.toLinearMap.normDet * volume A := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change LipschitzOnWith C (f ∘ L.symm) (L '' S) at hf
  have hH := (hf.mono (image_mono hAS)).hausdorffMeasure_image_le
    (d := (n : ℝ)) (by positivity)
  have himage : (f ∘ L.symm) '' (L '' A) = f '' A := by
    rw [image_image]
    congr 1
    ext x
    simp only [Function.comp_apply, L.symm_apply_apply]
  have hL := L.toLinearMap.hausdorffMeasure_image A
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hL
  change Measure.hausdorffMeasure (n : ℝ) (L '' A) =
    ENNReal.ofReal L.toLinearMap.normDet * Measure.hausdorffMeasure (n : ℝ) A at hL
  rw [himage, ENNReal.rpow_natCast, hL] at hH
  have hcal : euclideanVolumeCalibration n * Measure.hausdorffMeasure (n : ℝ) A =
      volume A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦ μ A)
        (euclideanVolumeCalibration_smul_hausdorff n)
  change euclideanVolumeCalibration n * Measure.hausdorffMeasure (n : ℝ) (f '' A) ≤ _
  calc
    _ ≤ euclideanVolumeCalibration n *
        ((C : ℝ≥0∞) ^ n * (ENNReal.ofReal L.toLinearMap.normDet *
          Measure.hausdorffMeasure (n : ℝ) A)) := mul_le_mul_right hH _
    _ = (C : ℝ≥0∞) ^ n * ENNReal.ofReal L.toLinearMap.normDet *
        (euclideanVolumeCalibration n * Measure.hausdorffMeasure (n : ℝ) A) := by ac_rfl
    _ = _ := by rw [hcal]

set_option backward.isDefEq.respectTransparency false in

theorem normDet_volume_le_calibratedMetricVolume_image
    (g : RiemannianMetric n M) (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] Y)
    {f : EuclideanSpace ℝ (Fin n) → M} {k : M → Y}
    {S A : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ≥0} (hAS : A ⊆ S)
    (hleft : ∀ x ∈ S, k (f x) = L x)
    (hk :
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      LipschitzOnWith C k (f '' S)) :
    ENNReal.ofReal L.toLinearMap.normDet * volume A ≤
      (C : ℝ≥0∞) ^ n * calibratedMetricVolume g (f '' A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change LipschitzOnWith C k (f '' S) at hk
  have hH := (hk.mono (image_mono hAS)).hausdorffMeasure_image_le
    (d := (n : ℝ)) (by positivity)
  have himage : k '' (f '' A) = L '' A := by
    rw [image_image]
    exact image_congr fun x hx ↦ hleft x (hAS hx)
  have hL := L.toLinearMap.hausdorffMeasure_image A
  simp only [finrank_euclideanSpace, Fintype.card_fin] at hL
  change Measure.hausdorffMeasure (n : ℝ) (L '' A) =
    ENNReal.ofReal L.toLinearMap.normDet * Measure.hausdorffMeasure (n : ℝ) A at hL
  rw [himage, ENNReal.rpow_natCast, hL] at hH
  have hcal : euclideanVolumeCalibration n * Measure.hausdorffMeasure (n : ℝ) A =
      volume A := by
    simpa only [Measure.smul_apply, smul_eq_mul] using
      congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦ μ A)
        (euclideanVolumeCalibration_smul_hausdorff n)
  calc
    _ = euclideanVolumeCalibration n *
        (ENNReal.ofReal L.toLinearMap.normDet * Measure.hausdorffMeasure (n : ℝ) A) := by
      rw [← hcal]
      ac_rfl
    _ ≤ euclideanVolumeCalibration n *
        ((C : ℝ≥0∞) ^ n * Measure.hausdorffMeasure (n : ℝ) (f '' A)) :=
      mul_le_mul_right hH _
    _ = _ := by
      change _ = (C : ℝ≥0∞) ^ n *
        (euclideanVolumeCalibration n * Measure.hausdorffMeasure (n : ℝ) (f '' A))
      ac_rfl

end PoincareConjecture.M10
