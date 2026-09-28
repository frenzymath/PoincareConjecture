import PoincareConjecture.Proofs.M10.Calibration

set_option autoImplicit false

open MeasureTheory Set
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.M10

theorem euclideanHausdorff_eq_zero_of_volume_eq_zero {n : ℕ}
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : volume A = 0) :
    Measure.hausdorffMeasure (n : ℝ) A = 0 := by
  have h := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin n)) ↦ μ A)
    (euclideanVolumeCalibration_smul_hausdorff n)
  simp only [Measure.smul_apply, smul_eq_mul, hA] at h
  exact (mul_eq_zero.mp h).resolve_left (euclideanVolumeCalibration_pos n).ne'

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]

set_option backward.isDefEq.respectTransparency false in

theorem calibratedMetricVolume_image_eq_zero_of_lipschitz
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {S A : Set (EuclideanSpace ℝ (Fin n))} {C : ℝ≥0}
    (hAS : A ⊆ S) (hA : volume A = 0)
    (hf :
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
          (TangentSpace (𝓡 n) : M → Type _) :=
        ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
      LipschitzOnWith C f S) :
    calibratedMetricVolume g (f '' A) = 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  change LipschitzOnWith C f S at hf
  have hH := (hf.mono hAS).hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity)
  rw [euclideanHausdorff_eq_zero_of_volume_eq_zero hA, mul_zero] at hH
  have hnull : Measure.hausdorffMeasure (n : ℝ) (f '' A) = 0 := bot_unique hH
  delta calibratedMetricVolume
  simp only [Measure.smul_apply, hnull, smul_zero]

end PoincareConjecture.M10
