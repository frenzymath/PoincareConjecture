import PoincareConjecture.Proofs.M10.CalibratedTransport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Comparison.LocalMeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.InverseMeasure
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.MeasureGluing
import Mathlib.Analysis.SpecificLimits.Basic




















set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem calibratedMetricVolume_image_eq_withDensity (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hAsource : A ⊆ e.source) :
    calibratedMetricVolume g (e '' A) =
      (volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) A := by
  let μ := calibratedMetricVolume g
  let pulled := (μ.restrict e.target).map e.symm
  let ν := volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))
  let r : ℕ → ℝ≥0 := fun k ↦ 1 + 1 / ((k : ℝ≥0) + 1)
  have hr : ∀ k, (1 : ℝ) < r k := by
    intro k
    have h : (1 : ℝ≥0) < r k := lt_add_of_pos_right _ (by positivity)
    exact_mod_cast h
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := (1 : ℝ≥0))).add tendsto_one_div_add_atTop_nhds_zero_nat
  let c : ℕ → ℝ≥0∞ := fun k ↦ (r k : ℝ≥0∞) ^ (n + 1)
  have hc : Tendsto c atTop (𝓝 1) := by
    simpa only [c, Function.comp_apply, ENNReal.coe_one, one_pow] using
      ENNReal.Tendsto.pow (n := n + 1)
        ((ENNReal.continuous_coe.tendsto (1 : ℝ≥0)).comp hrt)
  have hlocal : ∀ k, ∀ x ∈ e.source,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → B ⊆ V →
          pulled B ≤ c k * ν B ∧ ν B ≤ c k * pulled B := by
    intro k x hx
    obtain ⟨V, hVo, hxV, hVsource, hbound⟩ :=
      local_calibratedMeasure_density_comparison g e he hei hx (hr k)
    refine ⟨V, hVo, hxV, ?_⟩
    intro B hB hBV
    have hmap : pulled B = μ (e '' B) :=
      map_inverse_restrict_apply e μ hB (hBV.trans hVsource)
    rw [hmap]
    exact hbound B hB hBV
  have hforward : ∀ k, ∀ x ∈ e.source,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → B ⊆ V →
          pulled B ≤ c k * ν B := by
    intro k x hx
    obtain ⟨V, hVo, hxV, hbound⟩ := hlocal k x hx
    exact ⟨V, hVo, hxV, fun B hB hBV ↦ (hbound B hB hBV).1⟩
  have hreverse : ∀ k, ∀ x ∈ e.source,
      ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧
        ∀ B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet B → B ⊆ V →
          ν B ≤ c k * pulled B := by
    intro k x hx
    obtain ⟨V, hVo, hxV, hbound⟩ := hlocal k x hx
    exact ⟨V, hVo, hxV, fun B hB hBV ↦ (hbound B hB hBV).2⟩
  have h := measure_eq_of_local_comparisons c hc hforward hreverse hA hAsource
  rwa [map_inverse_restrict_apply e μ hA hAsource] at h


theorem calibratedMetricVolume_image_eq_lintegral (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {A : Set (EuclideanSpace ℝ (Fin n))} (hA : MeasurableSet A)
    (hAsource : A ⊆ e.source) :
    calibratedMetricVolume g (e '' A) =
      ∫⁻ y in A, ENNReal.ofReal (pullbackJacobian g e y) := by
  rw [calibratedMetricVolume_image_eq_withDensity g e he hei hA hAsource,
    withDensity_apply _ hA]

end PoincareConjecture.SurgeryVolume.Measure
