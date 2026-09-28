import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Homothety.Length
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Basic

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle NNReal ENNReal

namespace PoincareConjecture.Homothety

variable {n : ℕ} {M : Type*} {N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]

theorem homothety_volume_image (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) (E : Set M) :
    calibratedMetricVolume h (f '' E) =
      ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * calibratedMetricVolume g E := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let c : ℝ≥0 := ⟨Real.sqrt Q, Real.sqrt_nonneg Q⟩
  have hc : (c : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt Q) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by
    rw [hc]
    exact (ENNReal.ofReal_pos.2 (Real.sqrt_pos.2 hQ)).ne'
  have hforward : LipschitzWith c f := by
    intro x y
    change h.edist (f x) (f y) ≤ (c : ℝ≥0∞) * g.edist x y
    rw [homothety_edist g h f Q hQ hf, hc]
  have hreverse : AntilipschitzWith c⁻¹ f := by
    intro x y
    change g.edist x y ≤ ((c⁻¹ : ℝ≥0) : ℝ≥0∞) * h.edist (f x) (f y)
    rw [homothety_edist g h f Q hQ hf, ← hc, ENNReal.coe_inv (ENNReal.coe_ne_zero.1 hc0),
      ENNReal.inv_mul_cancel_left hc0 ENNReal.coe_ne_top]
  have hmeasure : Measure.hausdorffMeasure (n : ℝ) (f '' E) =
      (c : ℝ≥0∞) ^ (n : ℝ) * Measure.hausdorffMeasure (n : ℝ) E := by
    apply le_antisymm (hforward.hausdorffMeasure_image_le (Nat.cast_nonneg n) E)
    have hrev := hreverse.le_hausdorffMeasure_image (Nat.cast_nonneg n) E
    rw [ENNReal.coe_inv (ENNReal.coe_ne_zero.1 hc0), ENNReal.inv_rpow] at hrev
    have hcPow0 : (c : ℝ≥0∞) ^ (n : ℝ) ≠ 0 := by
      simpa only [ENNReal.rpow_natCast] using pow_ne_zero n hc0
    have hcPowTop : (c : ℝ≥0∞) ^ (n : ℝ) ≠ ⊤ := by
      simpa only [ENNReal.rpow_natCast] using
        (ENNReal.pow_ne_top ENNReal.coe_ne_top : (c : ℝ≥0∞) ^ n ≠ ⊤)
    calc
      (c : ℝ≥0∞) ^ (n : ℝ) * Measure.hausdorffMeasure (n : ℝ) E ≤
          (c : ℝ≥0∞) ^ (n : ℝ) *
            (((c : ℝ≥0∞) ^ (n : ℝ))⁻¹ * Measure.hausdorffMeasure (n : ℝ) (f '' E)) :=
        mul_le_mul_right hrev _
      _ = Measure.hausdorffMeasure (n : ℝ) (f '' E) :=
        ENNReal.mul_inv_cancel_left hcPow0 hcPowTop
  have hfactor : (c : ℝ≥0∞) ^ (n : ℝ) = ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) := by
    rw [hc, ENNReal.ofReal_rpow_of_pos (Real.sqrt_pos.2 hQ),
      ← Real.rpow_div_two_eq_sqrt (n : ℝ) hQ.le, Real.rpow_eq_pow]
  change (euclideanVolumeCalibration n • Measure.hausdorffMeasure (n : ℝ)) (f '' E) =
    ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) *
      (euclideanVolumeCalibration n • Measure.hausdorffMeasure (n : ℝ)) E
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [hmeasure, hfactor, mul_left_comm]

theorem homothety_volume_map (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (Q : ℝ) (hQ : 0 < Q)
    (hf : MetricHomothety g h f Q) :
    calibratedMetricVolume h = ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) •
      Measure.map f (calibratedMetricVolume g) := by
  ext E hE
  rw [Measure.smul_apply, smul_eq_mul, Measure.map_apply f.continuous.measurable hE]
  calc
    calibratedMetricVolume h E = calibratedMetricVolume h (f '' (f ⁻¹' E)) := by
      exact congrArg (calibratedMetricVolume h)
        (Set.image_preimage_eq E (show Function.Surjective f from f.toEquiv.surjective)).symm
    _ = ENNReal.ofReal (Real.rpow Q ((n : ℝ) / 2)) * calibratedMetricVolume g (f ⁻¹' E) :=
      homothety_volume_image g h f Q hQ hf (f ⁻¹' E)

end PoincareConjecture.Homothety
