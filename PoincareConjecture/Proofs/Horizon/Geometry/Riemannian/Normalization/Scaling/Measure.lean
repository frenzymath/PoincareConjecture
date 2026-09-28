import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic








noncomputable section
set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem rescaledMetric_volumeMeasure (g : RiemannianMetric n M) (c : ℝ)
    (hc : 0 < c) :
    (rescaledMetric g c hc).volumeMeasure =
      ENNReal.ofReal (Real.sqrt c) ^ n • g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₁ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let H₁ := @Measure.hausdorffMeasure M m₁ inferInstance inferInstance (n : ℝ)
  let g' := rescaledMetric g c hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₂ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let H₂ := @Measure.hausdorffMeasure M m₂ inferInstance inferInstance (n : ℝ)
  let C : ℝ≥0 := ⟨Real.sqrt c, Real.sqrt_nonneg c⟩
  have hCeq : (C : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt c) :=
    ENNReal.ofReal_coe_nnreal.symm
  have hCne : C ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hne : (C : ℝ≥0∞) ≠ 0 := by
    rw [hCeq]
    exact (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr hc)).ne'
  have hLip : @LipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C id := by
    intro x y
    change g'.edist x y ≤ (C : ℝ≥0∞) * g.edist x y
    rw [rescaledMetric_edist, ← hCeq]
  have hAnti : @AntilipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C⁻¹ id := by
    intro x y
    change g.edist x y ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * g'.edist x y
    rw [rescaledMetric_edist, ENNReal.coe_inv hCne, ← hCeq]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]
  have hH : H₂ = (C : ℝ≥0∞) ^ n • H₁ := by
    ext s hs
    have hup : H₂ s ≤ (C : ℝ≥0∞) ^ n * H₁ s := by
      simpa only [Set.image_id, ENNReal.rpow_natCast] using
        (@LipschitzWith.hausdorffMeasure_image_le M M m₁ m₂
          inferInstance inferInstance inferInstance inferInstance (K := C) (f := id)
          hLip (d := (n : ℝ)) (by positivity) s)
    have hlo : H₁ s ≤ ((C : ℝ≥0∞) ^ n)⁻¹ * H₂ s := by
      simpa only [Set.image_id, ENNReal.rpow_natCast,
        ENNReal.coe_inv hCne, ENNReal.inv_pow] using
        (@AntilipschitzWith.le_hausdorffMeasure_image M M m₁ m₂
          inferInstance inferInstance inferInstance inferInstance (K := C⁻¹) (f := id)
          (d := (n : ℝ)) hAnti (by positivity) s)
    have hmul : (C : ℝ≥0∞) ^ n * H₁ s ≤
        (C : ℝ≥0∞) ^ n * (((C : ℝ≥0∞) ^ n)⁻¹ * H₂ s) := by
      gcongr
    rw [← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ hne)
      (ENNReal.pow_ne_top ENNReal.coe_ne_top), one_mul] at hmul
    exact le_antisymm hup hmul
  change _ • H₂ = ENNReal.ofReal (Real.sqrt c) ^ n • (_ • H₁)
  rw [hH, hCeq, smul_comm]

end PoincareConjecture
