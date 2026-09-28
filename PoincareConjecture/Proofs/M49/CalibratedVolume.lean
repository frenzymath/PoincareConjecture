import PoincareConjecture.Proofs.M10.CalibratedTransport
import PoincareConjecture.Definitions.Ch15.SurgeryFlow

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M49

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]

theorem calibratedMetricVolume_isLocallyFinite (g : RiemannianMetric n M) :
    IsLocallyFiniteMeasure (calibratedMetricVolume g) := by
  constructor
  intro p
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  let x := chartAt (EuclideanSpace ℝ (Fin n)) p p
  have hx : x ∈ e.source := (chartAt (EuclideanSpace ℝ (Fin n)) p).map_source
    (mem_chart_source _ _)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target := contMDiffOn_chart
  have hJ := M10.pullbackJacobian_continuousAt g
    (he.contMDiffAt (e.open_source.mem_nhds hx))
  have hbound : ∀ᶠ y in 𝓝 x,
      M10.pullbackJacobian g e y < M10.pullbackJacobian g e x + 1 :=
    hJ.eventually (gt_mem_nhds (lt_add_one _))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds hx) hbound)
  have hsource : Metric.ball x r ⊆ e.source := fun y hy => (hball hy).1
  have hopen : IsOpen (e '' Metric.ball x r) :=
    e.isOpen_image_of_subset_source Metric.isOpen_ball hsource
  have hp : p ∈ e '' Metric.ball x r := by
    refine ⟨x, Metric.mem_ball_self hr, ?_⟩
    exact (chartAt (EuclideanSpace ℝ (Fin n)) p).left_inv (mem_chart_source _ _)
  refine ⟨e '' Metric.ball x r, hopen.mem_nhds hp, ?_⟩
  rw [M10.calibratedMetricVolume_image_eq_lintegral g e he hei
    measurableSet_ball hsource]
  calc
    _ ≤ ∫⁻ _y in Metric.ball x r,
        ENNReal.ofReal (M10.pullbackJacobian g e x + 1) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ENNReal.ofReal_le_ofReal (hball hy).2.le
    _ < (⊤ : ℝ≥0∞) := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

theorem calibratedMetricVolume_lt_top_of_isCompact (g : RiemannianMetric n M)
    {K : Set M} (hK : IsCompact K) : calibratedMetricVolume g K < ⊤ := by
  let := calibratedMetricVolume_isLocallyFinite g
  exact hK.measure_lt_top

theorem sliceVolume_lt_top (F : SurgeryFlowData.{u}) {t : ℝ}
    (ht : t ∈ F.time_domain) : calibratedMetricVolume (F.metric t) univ < ⊤ :=
  calibratedMetricVolume_lt_top_of_isCompact (F.metric t) (F.slices_compact t ht)

theorem initialVolume_ne_top (F : SurgeryFlowData.{u}) :
    calibratedMetricVolume (F.metric 0) univ ≠ ⊤ :=
  (sliceVolume_lt_top F F.zero_mem).ne

end PoincareConjecture.M49
