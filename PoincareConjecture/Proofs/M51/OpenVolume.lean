import PoincareConjecture.Proofs.M10.CalibratedPositive









set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M51

open M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem calibratedMetricVolume_open_pos (g : RiemannianMetric n M)
    {U : Set M} (hU : IsOpen U) (hne : U.Nonempty) :
    0 < calibratedMetricVolume g U := by
  obtain ⟨p, hp⟩ := hne
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  let A := e.source ∩ e ⁻¹' U
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := contMDiffOn_chart
  have heD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hA : IsOpen A := e.isOpen_inter_preimage hU
  have hAsource : A ⊆ e.source := inter_subset_left
  have hAne : A.Nonempty := by
    refine ⟨chartAt (EuclideanSpace ℝ (Fin n)) p p, ?_, ?_⟩
    · exact (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source (mem_chart_source _ _)
    · change (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
        (chartAt (EuclideanSpace ℝ (Fin n)) p p) ∈ U
      simpa only [(chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv
        (mem_chart_source _ _)] using hp
  have hj : AEMeasurable (fun y ↦ ENNReal.ofReal (pullbackJacobian g e y))
      (volume.restrict A) :=
    (ENNReal.continuous_ofReal.comp_continuousOn (fun y hy ↦
      (pullbackJacobian_continuousAt g (he.contMDiffAt
        (e.open_source.mem_nhds (hAsource hy)))).continuousWithinAt)).aemeasurable
      hA.measurableSet
  have hmass : 0 < ∫⁻ y in A, ENNReal.ofReal (pullbackJacobian g e y) := by
    apply bot_lt_iff_ne_bot.mpr
    intro hz
    obtain ⟨y, hy, hzero⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
      (hA.measure_ne_zero volume hAne) ((lintegral_eq_zero_iff' hj).mp hz)
    exact (ENNReal.ofReal_pos.mpr
      (pullbackJacobian_pos g (heD.mfderiv_bijective (hAsource hy)).injective)).ne' hzero
  rw [← M10.calibratedMetricVolume_image_eq_lintegral g e he hei
    hA.measurableSet hAsource] at hmass
  exact hmass.trans_le (measure_mono (by
    rintro _ ⟨y, hy, rfl⟩
    exact hy.2))


theorem calibratedMetricVolume_component_pos (g : RiemannianMetric n M) (x : M) :
    0 < calibratedMetricVolume g (connectedComponent x) := by
  let : LocallyConnectedSpace M :=
    ChartedSpace.locallyConnectedSpace (EuclideanSpace ℝ (Fin n)) M
  exact calibratedMetricVolume_open_pos g isOpen_connectedComponent
    ⟨x, mem_connectedComponent⟩

end PoincareConjecture.M51
