import PoincareConjecture.Proofs.M01.NormalizationScaling
import PoincareConjecture.Proofs.M01.NormalizationVolume

set_option autoImplicit false

open Bundle Manifold MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem m01RescaledMetric_ball [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric 3 M) (c : ℝ) (hc : 0 < c)
    (x : M) (r : ℝ) :
    (m01RescaledMetric g c hc).ball x r = g.ball x (r / Real.sqrt c) := by
  have hsqrt : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hne : ENNReal.ofReal (Real.sqrt c) ≠ 0 := (ENNReal.ofReal_pos.mpr hsqrt).ne'
  ext y
  simp only [RiemannianMetric.ball, Set.mem_ofPred_eq, m01RescaledMetric_edist,
    ENNReal.ofReal_div_of_pos hsqrt]
  rw [ENNReal.lt_div_iff_mul_lt (Or.inl hne) (Or.inl ENNReal.ofReal_ne_top), mul_comm]

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem m01RescaledMetric_hausdorffVolume (g : RiemannianMetric 3 M) (c : ℝ)
    (hc : 0 < c) (s : Set M) :
    (m01RescaledMetric g c hc).hausdorffVolume s =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * g.hausdorffVolume s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₁ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hvol₁ : @Measure.hausdorffMeasure M m₁ inferInstance inferInstance (3 : ℝ) =
      g.hausdorffVolume := rfl
  let g' := m01RescaledMetric g c hc
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g'.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g'.inner, g'.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let m₂ : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  have hvol₂ : @Measure.hausdorffMeasure M m₂ inferInstance inferInstance (3 : ℝ) =
      g'.hausdorffVolume := rfl
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
    rw [m01RescaledMetric_edist, ← hCeq]
  have hAnti : @AntilipschitzWith M M m₁.toPseudoEMetricSpace m₂.toPseudoEMetricSpace C⁻¹ id := by
    intro x y
    change g.edist x y ≤ ((C⁻¹ : ℝ≥0) : ℝ≥0∞) * g'.edist x y
    rw [m01RescaledMetric_edist, ENNReal.coe_inv hCne, ← hCeq]
    rw [← mul_assoc, ENNReal.inv_mul_cancel hne ENNReal.coe_ne_top, one_mul]
  have hup : g'.hausdorffVolume s ≤ (C : ℝ≥0∞) ^ 3 * g.hausdorffVolume s := by
    simpa only [Set.image_id, Nat.cast_ofNat, ENNReal.rpow_ofNat, hvol₁, hvol₂] using
      (@LipschitzWith.hausdorffMeasure_image_le M M m₁ m₂
        inferInstance inferInstance inferInstance inferInstance (K := C) (f := id)
        hLip (d := (3 : ℕ)) (by positivity) s)
  have hlo : g.hausdorffVolume s ≤ ((C : ℝ≥0∞) ^ 3)⁻¹ * g'.hausdorffVolume s := by
    simpa only [Set.image_id, Nat.cast_ofNat, ENNReal.rpow_ofNat,
      ENNReal.coe_inv hCne, ENNReal.inv_pow, hvol₁, hvol₂] using
      (@AntilipschitzWith.le_hausdorffMeasure_image M M m₁ m₂
        inferInstance inferInstance inferInstance inferInstance (K := C⁻¹) (f := id)
        (d := (3 : ℕ)) hAnti (by positivity) s)
  have hmul : (C : ℝ≥0∞) ^ 3 * g.hausdorffVolume s ≤
      (C : ℝ≥0∞) ^ 3 * (((C : ℝ≥0∞) ^ 3)⁻¹ * g'.hausdorffVolume s) := by
    gcongr
  rw [← mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero _ hne)
    (ENNReal.pow_ne_top ENNReal.coe_ne_top), one_mul] at hmul
  simpa only [hCeq] using le_antisymm hup hmul

theorem m01RescaledMetric_normalizedMetricVolume (g : RiemannianMetric 3 M) (c : ℝ)
    (hc : 0 < c) (s : Set M) :
    normalizedMetricVolume (m01RescaledMetric g c hc) s =
      ENNReal.ofReal (Real.sqrt c) ^ 3 * normalizedMetricVolume g s := by
  simp only [normalizedMetricVolume, Measure.smul_apply, smul_eq_mul,
    m01RescaledMetric_hausdorffVolume]
  ac_rfl

end PoincareConjecture
