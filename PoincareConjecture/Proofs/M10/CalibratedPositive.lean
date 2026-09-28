import PoincareConjecture.Proofs.M10.CalibratedTransport
import Mathlib.MeasureTheory.Measure.OpenPos









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem calibratedMetricVolume_univ_pos (g : RiemannianMetric n M) (p : M) :
    0 < calibratedMetricVolume g univ := by
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := contMDiffOn_chart
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hsource : e.source.Nonempty :=
    ⟨chartAt (EuclideanSpace ℝ (Fin n)) p p,
      (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source (mem_chart_source _ _)⟩
  have hj : AEMeasurable (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))
      (volume.restrict e.source) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (fun y hy ↦
      (pullbackJacobian_continuousAt g (he.contMDiffAt
        (e.open_source.mem_nhds hy))).continuousWithinAt)).aemeasurable
      e.open_source.measurableSet
  have hmass : 0 < ∫⁻ y in e.source, ENNReal.ofReal (pullbackJacobian g e y) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    obtain ⟨y, hy, hzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (e.open_source.measure_ne_zero volume hsource) ((lintegral_eq_zero_iff' hj).mp hz)
    have hpos := ENNReal.ofReal_pos.mpr
      (pullbackJacobian_pos g (heD.mfderiv_bijective hy).injective)
    exact hpos.ne' hzero
  have himage := calibratedMetricVolume_image_eq_lintegral g e he hei
    e.open_source.measurableSet (Subset.refl e.source)
  rw [← himage] at hmass
  exact hmass.trans_le (measure_mono (subset_univ _))

end PoincareConjecture.M10
