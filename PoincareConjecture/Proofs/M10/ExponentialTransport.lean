import PoincareConjecture.Proofs.M10.CalibratedPushforward
import PoincareConjecture.Proofs.M10.ExponentialSlice
import PoincareConjecture.Proofs.M10.RegularImage

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

noncomputable def exponentialSliceJacobian (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (z : EuclideanSpace ℝ (Fin n)) : ℝ :=
  pullbackJacobian (F.metric (T - τ)) (exponentialSliceChart G τ) z

theorem exponentialSliceJacobian_nonneg (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    0 ≤ exponentialSliceJacobian G τ z :=
  pullbackJacobian_nonneg _ _ _

theorem exponentialSliceJacobian_continuousOn (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) :
    ContinuousOn (exponentialSliceJacobian G τ) (exponentialSliceChart G τ).source := by
  intro z hz
  exact (pullbackJacobian_continuousAt _
    (((exponentialSliceChart_contMDiffOn G τ).contMDiffAt
      ((exponentialSliceChart G τ).open_source.mem_nhds hz)).of_le (by simp))).continuousWithinAt

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem map_exponentialSliceJacobian_eq_restrict (G : LExponentialGeometry F T τmax p)
    (τ : ℝ) :
    ((volume.withDensity (fun z ↦ ENNReal.ofReal (exponentialSliceJacobian G τ z))).restrict
      (exponentialSliceChart G τ).source).map (exponentialSliceChart G τ) =
        (calibratedMetricVolume (F.metric (T - τ))).restrict
          (exponentialSliceChart G τ).target := by
  exact map_pullbackJacobian_eq_calibratedMetricVolume _ _
    ((exponentialSliceChart_contMDiffOn G τ).of_le (by simp))
    ((exponentialSliceChart_symm_contMDiffOn G τ).of_le (by simp))

variable [ConnectedSpace M]

theorem calibratedMetricVolume_restrict_exponentialSlice_target
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    (calibratedMetricVolume (F.metric (T - τ))).restrict
      (exponentialSliceChart G τ).target = calibratedMetricVolume (F.metric (T - τ)) := by
  apply Measure.restrict_eq_self_of_ae_mem
  exact ae_iff.mpr (regularImage_slice_complement_eq_zero hL hDifferential hwindow G hτ hmax)

theorem map_exponentialSliceJacobian_eq_calibratedMetricVolume
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    ((volume.withDensity (fun z ↦ ENNReal.ofReal (exponentialSliceJacobian G τ z))).restrict
      (exponentialSliceChart G τ).source).map (exponentialSliceChart G τ) =
        calibratedMetricVolume (F.metric (T - τ)) := by
  rw [map_exponentialSliceJacobian_eq_restrict,
    calibratedMetricVolume_restrict_exponentialSlice_target hL hDifferential hwindow G hτ hmax]

theorem lintegral_eq_exponentialSliceJacobian
    (hL : LGeodesicTheory F T τmax)
    (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (hwindow : Icc (T - τmax) T ⊆ J) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) {f : M → ℝ≥0∞}
    (hf : AEMeasurable f (calibratedMetricVolume (F.metric (T - τ)))) :
    ∫⁻ q, f q ∂calibratedMetricVolume (F.metric (T - τ)) =
      ∫⁻ z in (exponentialSliceChart G τ).source,
        ENNReal.ofReal (exponentialSliceJacobian G τ z) * f (exponentialSliceChart G τ z) := by
  let e := exponentialSliceChart G τ
  let j := fun z ↦ ENNReal.ofReal (exponentialSliceJacobian G τ z)
  have hj : AEMeasurable j (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn
      (exponentialSliceJacobian_continuousOn G τ)).aemeasurable e.open_source.measurableSet
  have hmap := map_exponentialSliceJacobian_eq_calibratedMetricVolume
    hL hDifferential hwindow G hτ hmax
  have he : AEMeasurable e ((volume.withDensity j).restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  have hfm : AEMeasurable f (((volume.withDensity j).restrict e.source).map e) :=
    hmap.symm ▸ hf
  have hfe : AEMeasurable (fun z ↦ f (e z)) ((volume.restrict e.source).withDensity j) := by
    rw [← restrict_withDensity e.open_source.measurableSet]
    exact hfm.comp_aemeasurable he
  calc
    _ = ∫⁻ z in e.source, f (e z) ∂volume.withDensity j := by
      rw [← hmap]
      exact lintegral_map' hfm he
    _ = _ := by
      rw [restrict_withDensity e.open_source.measurableSet]
      exact lintegral_withDensity_eq_lintegral_mul₀' hj hfe

end PoincareConjecture.M10
