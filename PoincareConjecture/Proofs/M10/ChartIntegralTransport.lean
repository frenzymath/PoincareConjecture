import PoincareConjecture.Proofs.M10.CalibratedPushforward
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem integrableOn_calibrated_iff_pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hρ : ContinuousOn (pullbackJacobian g e) e.source) {f : M → ℝ}
    (hf : AEStronglyMeasurable f ((calibratedMetricVolume g).restrict e.target)) :
    IntegrableOn f e.target (calibratedMetricVolume g) ↔
      IntegrableOn (fun y ↦ pullbackJacobian g e y * f (e y)) e.source volume := by
  have hmap := map_pullbackJacobian_eq_calibratedMetricVolume g e he hei
  have hm := e.continuousOn.aemeasurable (μ := volume.withDensity
    (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) e.open_source.measurableSet
  have hf' := hf
  rw [← hmap] at hf'
  change Integrable f _ ↔ _
  rw [← hmap, integrable_map_measure hf' hm, restrict_withDensity e.open_source.measurableSet]
  rw [integrable_withDensity_iff_integrable_smul₀'
    (hρ.aemeasurable e.open_source.measurableSet).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))]
  simp only [Function.comp_apply, ENNReal.toReal_ofReal (pullbackJacobian_nonneg g e _),
    smul_eq_mul, IntegrableOn]


theorem integralOn_calibrated_eq_pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hρ : ContinuousOn (pullbackJacobian g e) e.source) {f : M → ℝ}
    (hf : AEStronglyMeasurable f ((calibratedMetricVolume g).restrict e.target)) :
    (∫ q in e.target, f q ∂calibratedMetricVolume g) =
      ∫ y in e.source, pullbackJacobian g e y * f (e y) := by
  have hmap := map_pullbackJacobian_eq_calibratedMetricVolume g e he hei
  have hm := e.continuousOn.aemeasurable (μ := volume.withDensity
    (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))) e.open_source.measurableSet
  rw [← hmap] at hf ⊢
  rw [integral_map hm hf, setIntegral_withDensity_eq_setIntegral_toReal_smul₀
    (hρ.aemeasurable e.open_source.measurableSet).ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ ↦ ENNReal.ofReal_lt_top))
    (fun y ↦ f (e y)) e.open_source.measurableSet]
  simp only [ENNReal.toReal_ofReal (pullbackJacobian_nonneg g e _), smul_eq_mul]

end PoincareConjecture.M10
