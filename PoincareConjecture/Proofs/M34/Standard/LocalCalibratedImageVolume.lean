import PoincareConjecture.Proofs.M34.Standard.LocalMapMetricComparison
import PoincareConjecture.Proofs.M34.Standard.CalibratedMetricComparison
import PoincareConjecture.Proofs.M34.Standard.LocalInverseMetricBound
import PoincareConjecture.Proofs.M10.InverseMeasure
import PoincareConjecture.Proofs.M10.MeasureGluing

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

namespace PoincareConjecture.M34

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [MeasurableSpace N]
  [BorelSpace M] [BorelSpace N]

theorem calibratedMetricVolume_image_le_of_edist_le_on
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : M → N) (A : Set M) {C : ℝ≥0}
    (hbound : ∀ x ∈ A, ∀ y ∈ A,
      h.edist (f x) (f y) ≤ (C : ℝ≥0∞) * g.edist x y) :
    calibratedMetricVolume h (f '' A) ≤
      (C : ℝ≥0∞) ^ n * calibratedMetricVolume g A := by
  let : EMetricSpace M := g.comparisonEMetric
  let : EMetricSpace N := h.comparisonEMetric
  have hLip : LipschitzOnWith C f A := hbound
  have hH := hLip.hausdorffMeasure_image_le (d := (n : ℝ)) (by positivity)
  rw [ENNReal.rpow_natCast] at hH
  change euclideanVolumeCalibration n * _ ≤
    (C : ℝ≥0∞) ^ n * (euclideanVolumeCalibration n * _)
  calc
    _ ≤ euclideanVolumeCalibration n * ((C : ℝ≥0∞) ^ n * _) := mul_le_mul_right hH _
    _ = _ := by ac_rfl

theorem calibratedMetricVolume_image_le_of_local_tangentNorm_le
    [SecondCountableTopology M]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) ≤ C * g.tangentNorm x v)
    {A : Set M} (hA : MeasurableSet A) (hAsource : A ⊆ e.source) :
    calibratedMetricVolume h (e '' A) ≤
      ENNReal.ofReal C ^ n * calibratedMetricVolume g A := by
  let μ := calibratedMetricVolume h
  let pulled := (μ.restrict e.target).map e.symm
  have hlocal : ∀ x ∈ e.source, ∃ V : Set M, IsOpen V ∧ x ∈ V ∧
      ∀ B : Set M, MeasurableSet B → B ⊆ V →
        pulled B ≤ ENNReal.ofReal C ^ n * calibratedMetricVolume g B := by
    intro x hx
    obtain ⟨V, hVo, hxV, hVU, hV⟩ :=
      g.exists_open_edist_image_bound_of_tangentNorm_le h e e.open_source hf hC hbound hx
    refine ⟨V, hVo, hxV, fun B hB hBV => ?_⟩
    rw [M10.map_inverse_restrict_apply e μ hB (hBV.trans hVU)]
    have hb := calibratedMetricVolume_image_le_of_edist_le_on g h e B
      (C := Real.toNNReal C) (fun y hy z hz => hV y (hBV hy) z (hBV hz))
    simpa only [ENNReal.ofNNReal_toNNReal] using hb
  have hb := M10.measure_le_mul_of_local_comparison hlocal hA hAsource
  rwa [M10.map_inverse_restrict_apply e μ hA hAsource] at hb

theorem calibratedMetricVolume_le_mul_image_of_local_tangentNorm_lower
    [SecondCountableTopology N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hi : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ e.source, ∀ v : TangentSpace (𝓡 n) x,
      g.tangentNorm x v ≤ C * h.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v))
    {A : Set M} (hA : MeasurableSet A) (hAsource : A ⊆ e.source) :
    calibratedMetricVolume g A ≤ ENNReal.ofReal C ^ n * calibratedMetricVolume h (e '' A) := by
  have hImage : MeasurableSet (e '' A) := by
    rw [e.image_eq_target_inter_inv_preimage hAsource]
    have hpre : MeasurableSet ((fun y : e.target => e.symm y) ⁻¹' A) :=
      (continuousOn_iff_continuous_domRestrict.mp e.symm.continuousOn).measurable hA
    convert (MeasurableEmbedding.subtype_coe e.open_target.measurableSet).measurableSet_image.mpr
      hpre using 1
    ext y
    simp [and_comm]
  have htarget : e '' A ⊆ e.target := by
    rintro _ ⟨x, hx, rfl⟩
    exact e.map_source (hAsource hx)
  have hb := calibratedMetricVolume_image_le_of_local_tangentNorm_le h g e.symm hi hC
    (fun y hy v => g.inverse_tangentNorm_le_of_forward_lower_bound h e hf hi hy
      (hbound (e.symm y) (e.map_target hy)) v) hImage htarget
  have hback : e.symm '' (e '' A) = A := e.symm_image_image_of_subset_source hAsource
  rwa [hback] at hb

end PoincareConjecture.M34
