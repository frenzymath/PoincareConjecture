import PoincareConjecture.Proofs.M10.CalibratedTransport
import Mathlib.MeasureTheory.Integral.Lebesgue.Map








set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem map_pullbackJacobian_eq_calibratedMetricVolume (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target) :
    ((volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))).restrict
      e.source).map e = (calibratedMetricVolume g).restrict e.target := by
  let ν := volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))
  have hmeas : AEMeasurable e (ν.restrict e.source) :=
    e.continuousOn.aemeasurable e.open_source.measurableSet
  ext B hB
  rw [Measure.map_apply_of_aemeasurable hmeas hB,
    Measure.restrict_apply' e.open_source.measurableSet, Measure.restrict_apply hB]
  have hsub : MeasurableSet ((Subtype.val : e.source → EuclideanSpace ℝ (Fin n)) ⁻¹'
      (e ⁻¹' B)) := hB.preimage e.continuousOn.domRestrict.measurable
  have hA : MeasurableSet (e ⁻¹' B ∩ e.source) := by
    simpa only [Subtype.range_coe] using
      (MeasurableEmbedding.subtype_coe e.open_source.measurableSet).measurableSet_preimage.mp hsub
  have himage := calibratedMetricVolume_image_eq_withDensity g e he hei hA inter_subset_right
  rw [image_preimage_inter, e.image_source_eq_target] at himage
  exact himage.symm


theorem lintegral_calibratedMetricVolume_eq_pullbackJacobian
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {F : M → ℝ≥0∞}
    (hF : AEMeasurable F ((calibratedMetricVolume g).restrict e.target)) :
    ∫⁻ q in e.target, F q ∂calibratedMetricVolume g =
      ∫⁻ y in e.source, F (e y)
        ∂volume.withDensity (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y)) := by
  have hmap := map_pullbackJacobian_eq_calibratedMetricVolume g e he hei
  rw [← hmap] at hF ⊢
  exact lintegral_map' hF (e.continuousOn.aemeasurable e.open_source.measurableSet)

end PoincareConjecture.M10
