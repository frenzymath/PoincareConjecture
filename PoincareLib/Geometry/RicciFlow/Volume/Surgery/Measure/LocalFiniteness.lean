import PoincareLib.Geometry.RicciFlow.Volume.Surgery.Measure.CalibratedTransport

/-!
Adapted from `PoincareMT/Proofs/M49/CalibratedVolume.lean` at
Mapher revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Finite calibrated volume on compact slices

Morgan-Tian, Lemma 17.12, p. 410, uses finite volume of the compact
slices. The M10 coordinate formula for the actual calibrated Hausdorff
measure and continuity of its Gram density give local finiteness in every
dimension. See `proof-work/tasks/M49/derivations/01-foundations.md`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareMT.SurgeryVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M]

/-- The calibrated volume used in MT Lemma 17.12, p. 410, is locally finite. -/
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
  have hJ := SurgeryVolume.Measure.pullbackJacobian_continuousAt g
    (he.contMDiffAt (e.open_source.mem_nhds hx))
  have hbound : ∀ᶠ y in 𝓝 x,
      SurgeryVolume.Measure.pullbackJacobian g e y < SurgeryVolume.Measure.pullbackJacobian g e x + 1 :=
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
  rw [SurgeryVolume.Measure.calibratedMetricVolume_image_eq_lintegral g e he hei
    measurableSet_ball hsource]
  calc
    _ ≤ ∫⁻ _y in Metric.ball x r,
        ENNReal.ofReal (SurgeryVolume.Measure.pullbackJacobian g e x + 1) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      exact ENNReal.ofReal_le_ofReal (hball hy).2.le
    _ < (⊤ : ℝ≥0∞) := by
      simp only [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- Compact sets have finite actual volume, as used for slices in MT Lemma 17.12, p. 410. -/
theorem calibratedMetricVolume_lt_top_of_isCompact (g : RiemannianMetric n M)
    {K : Set M} (hK : IsCompact K) : calibratedMetricVolume g K < ⊤ := by
  let := calibratedMetricVolume_isLocallyFinite g
  exact hK.measure_lt_top

end PoincareMT.SurgeryVolume
