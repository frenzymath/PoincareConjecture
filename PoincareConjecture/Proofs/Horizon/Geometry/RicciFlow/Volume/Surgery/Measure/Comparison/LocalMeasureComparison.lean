import PoincareConjecture.Proofs.M10.LocalMeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Comparison.LocalMetricComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Coordinates.PullbackJacobian
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Comparison.CalibratedComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Measure.Comparison.DensityComparison

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture.SurgeryVolume.Measure

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]

set_option backward.isDefEq.respectTransparency false in

theorem local_calibratedMeasure_density_comparison (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ e.source)
    {r : ℝ≥0} (hr : (1 : ℝ) < r) :
    ∃ V : Set (EuclideanSpace ℝ (Fin n)), IsOpen V ∧ x ∈ V ∧ V ⊆ e.source ∧
      ∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A → A ⊆ V →
        calibratedMetricVolume g (e '' A) ≤ (r : ℝ≥0∞) ^ (n + 1) *
          (volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) A ∧
        (volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) A ≤
          (r : ℝ≥0∞) ^ (n + 1) * calibratedMetricVolume g (e '' A) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : MeasurableSpace (TangentSpace (𝓡 n) (e x)) := borel _
  let : BorelSpace (TangentSpace (𝓡 n) (e x)) := ⟨rfl⟩
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (e x) := heD.mfderiv hx
  have hL : ∀ v, ‖L v‖ = g.tangentNorm (e x) (mfderiv (𝓡 n) (𝓡 n) e x v) :=
    fun v ↦ norm_eq_sqrt_real_inner (L v)
  have hJL : ENNReal.ofReal L.toLinearMap.normDet =
      ENNReal.ofReal (pullbackJacobian g e x) := by
    congr 1
    exact (pullbackJacobian_eq_normDet g e x).symm
  obtain ⟨V, hVo, hxV, hVsource, hforward, hinverse⟩ :=
    local_normalized_metric_comparison g e he hei hx L hL hr
  have hJ := eventually_pullbackJacobian_comparison g
    (he.contMDiffAt (e.open_source.mem_nhds hx)) (heD.mfderiv_bijective hx).injective hr
  obtain ⟨W, hWsub, hWo, hxW⟩ := mem_nhds_iff.mp hJ
  refine ⟨V ∩ W, hVo.inter hWo, ⟨hxV, hxW⟩,
    inter_subset_left.trans hVsource, ?_⟩
  intro A hA hAVW
  have hAV : A ⊆ V := hAVW.trans inter_subset_left
  have hu := calibratedMetricVolume_image_le_of_normalized_lipschitz g L hAV hforward
  have hl := normDet_volume_le_calibratedMetricVolume_image g L hAV
    (fun y hy ↦ congrArg L (e.left_inv (hVsource hy))) hinverse
  rw [hJL] at hu hl
  have hd := withDensity_comparison_of_local_bounds volume hA (zero_lt_one.trans hr)
    (fun y hy ↦ (hWsub (hAVW hy).2).1) (fun y hy ↦ (hWsub (hAVW hy).2).2)
  constructor
  · calc
      _ ≤ (r : ℝ≥0∞) ^ n *
          (ENNReal.ofReal (pullbackJacobian g e x) * volume A) := by
        simpa only [mul_assoc] using hu
      _ ≤ (r : ℝ≥0∞) ^ n *
          ((r : ℝ≥0∞) * (volume.withDensity
            (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) A) :=
        mul_le_mul_right hd.1 _
      _ = _ := by rw [pow_succ, mul_assoc]
  · calc
      _ ≤ (r : ℝ≥0∞) *
          (ENNReal.ofReal (pullbackJacobian g e x) * volume A) := by
        simpa only [mul_assoc] using hd.2
      _ ≤ (r : ℝ≥0∞) *
          ((r : ℝ≥0∞) ^ n * calibratedMetricVolume g (e '' A)) :=
        mul_le_mul_right hl _
      _ = _ := by rw [pow_succ]; ac_rfl

end PoincareConjecture.SurgeryVolume.Measure
