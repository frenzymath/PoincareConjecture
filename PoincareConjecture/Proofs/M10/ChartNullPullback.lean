import PoincareConjecture.Proofs.M10.CalibratedPushforward









set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem ae_calibrated_pullback (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    (hρ : ContinuousOn (pullbackJacobian g e) e.source)
    {P : M → Prop} (hP : ∀ᵐ q ∂calibratedMetricVolume g, P q) :
    ∀ᵐ y ∂volume, y ∈ e.source → P (e y) := by
  let d := fun y ↦ ENNReal.ofReal (pullbackJacobian g e y)
  let ν := (volume.withDensity d).restrict e.source
  have hm : AEMeasurable e ν := e.continuousOn.aemeasurable e.open_source.measurableSet
  have hmap : ∀ᵐ q ∂ν.map e, P q := by
    rw [show ν.map e = (calibratedMetricVolume g).restrict e.target from
      map_pullbackJacobian_eq_calibratedMetricVolume g e he hei]
    exact ae_restrict_of_ae hP
  have hw : ∀ᵐ y ∂(volume.restrict e.source).withDensity d, P (e y) := by
    have h := ae_of_ae_map hm hmap
    simpa only [ν, restrict_withDensity e.open_source.measurableSet] using h
  have hd : AEMeasurable d (volume.restrict e.source) :=
    (hρ.aemeasurable e.open_source.measurableSet).ennreal_ofReal
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hdpos : ∀ᵐ y ∂volume.restrict e.source, d y ≠ 0 := by
    filter_upwards [ae_restrict_mem e.open_source.measurableSet] with y hy
    exact (ENNReal.ofReal_pos.mpr
      (pullbackJacobian_pos g (heD.mfderiv_bijective hy).injective)).ne'
  exact (ae_restrict_iff' e.open_source.measurableSet).mp
    (hw.filter_mono (withDensity_absolutelyContinuous' hd hdpos).ae_le)

end PoincareConjecture.M10
