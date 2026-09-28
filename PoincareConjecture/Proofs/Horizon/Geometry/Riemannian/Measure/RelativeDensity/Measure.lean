import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.RelativeDensity.Smooth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.HausdorffDensity
import Mathlib.Topology.Compactness.Lindelof

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem lintegral_target_eq_lintegral_pullback_density
    (g : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {F : M → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ y in e.target, F y ∂g.volumeMeasure) =
      ∫⁻ x in e.source, ENNReal.ofReal (g.pullbackVolumeDensity e x) * F (e x) := by
  have hmap := g.map_restrict_volumeMeasure_symm e he hei
  have hme : AEMeasurable (fun x => F (e x))
      ((g.volumeMeasure.restrict e.target).map e.symm) := by
    rw [hmap]
    exact hF.comp_aemeasurable
      (e.continuousOn.aemeasurable e.open_source.measurableSet)
  have hi := lintegral_map' hme
    (e.symm.continuousOn.aemeasurable e.open_target.measurableSet)
  change (∫⁻ x, F (e x) ∂(g.volumeMeasure.restrict e.target).map e.symm) =
    (∫⁻ y in e.target, F (e (e.symm y)) ∂g.volumeMeasure) at hi
  have hid : (∫⁻ y in e.target, F (e (e.symm y)) ∂g.volumeMeasure) =
      ∫⁻ y in e.target, F y ∂g.volumeMeasure := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    rw [e.right_inv hy]
  rw [hid, hmap, restrict_withDensity e.open_source.measurableSet] at hi
  rw [← hi]
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hρ : ContinuousOn (g.pullbackVolumeDensity e) e.source := by
    intro x hx
    exact (g.contDiffAt_pullbackVolumeDensity
      (he.contMDiffAt (e.open_source.mem_nhds hx))
      (hD.mfderiv_injective hx)).1.continuousAt.continuousWithinAt
  exact lintegral_withDensity_eq_lintegral_mul₀
    ((ENNReal.continuous_ofReal.comp_continuousOn hρ).aemeasurable
      e.open_source.measurableSet)
    (hF.comp_aemeasurable (e.continuousOn.aemeasurable e.open_source.measurableSet))

theorem restrict_volumeMeasure_eq_withDensity_relativeVolumeDensity
    (g h : RiemannianMetric n M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target) :
    g.volumeMeasure.restrict e.target =
      (h.volumeMeasure.withDensity
        (fun x => ENNReal.ofReal (g.relativeVolumeDensity h x))).restrict e.target := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  have hw : Measurable (fun x => ENNReal.ofReal (g.relativeVolumeDensity h x)) :=
    (ENNReal.continuous_ofReal.comp (g.continuous_relativeVolumeDensity h)).measurable
  ext B hB
  calc
    g.volumeMeasure.restrict e.target B =
        ∫⁻ y in e.target, B.indicator 1 y ∂g.volumeMeasure :=
      (lintegral_indicator_one hB).symm
    _ = ∫⁻ x in e.source,
        ENNReal.ofReal (g.pullbackVolumeDensity e x) * B.indicator 1 (e x) :=
      g.lintegral_target_eq_lintegral_pullback_density e he hei
        (measurable_const.indicator hB)
    _ = ∫⁻ x in e.source, ENNReal.ofReal (h.pullbackVolumeDensity e x) *
        B.indicator (fun y => ENNReal.ofReal (g.relativeVolumeDensity h y)) (e x) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
      by_cases hxB : e x ∈ B
      · simp only [indicator_of_mem hxB, Pi.one_apply, mul_one]
        rw [g.relativeVolumeDensity_eq_pullback_div h e x (hD.mfderiv_injective hx)]
        have hpos := (h.contDiffAt_pullbackVolumeDensity
          (he.contMDiffAt (e.open_source.mem_nhds hx)) (hD.mfderiv_injective hx)).2
        rw [← ENNReal.ofReal_mul hpos.le, ← mul_div_assoc, mul_div_cancel_left₀ _ hpos.ne']
      · simp only [indicator_of_notMem hxB, mul_zero]
    _ = ∫⁻ y in e.target,
        B.indicator (fun y => ENNReal.ofReal (g.relativeVolumeDensity h y)) y
          ∂h.volumeMeasure :=
      (h.lintegral_target_eq_lintegral_pullback_density e he hei (hw.indicator hB)).symm
    _ = (h.volumeMeasure.withDensity
        (fun y => ENNReal.ofReal (g.relativeVolumeDensity h y))).restrict e.target B := by
      rw [lintegral_indicator hB, Measure.restrict_restrict hB,
        Measure.restrict_apply hB, withDensity_apply _ (hB.inter e.open_target.measurableSet)]

theorem volumeMeasure_eq_withDensity_relativeVolumeDensity
    [SecondCountableTopology M] (g h : RiemannianMetric n M) :
    g.volumeMeasure = h.volumeMeasure.withDensity
      (fun x => ENNReal.ofReal (g.relativeVolumeDensity h x)) := by
  obtain ⟨T, hT, hcover⟩ := LindelofSpace.elim_nhds_subcover
    (fun p : M => (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (fun p => (chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds
      (mem_chart_source _ p))
  apply Measure.ext_of_biUnion_eq_univ hT hcover
  intro p _
  exact g.restrict_volumeMeasure_eq_withDensity_relativeVolumeDensity h
    (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
    contMDiffOn_chart_symm contMDiffOn_chart

end PoincareConjecture.RiemannianMetric
