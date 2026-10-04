import PoincareLib.Geometry.CurveShortening.Deformation.MinimalDisk.CompactDiskDerivative
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Differentiation using the genuine time-derivative trace

The derivative identity is required only in the open disk. Continuous traces
on a common compact time neighborhood supply the domination and all
integrability. Source: Morgan--Tian Lemma 19.2, printed p. 438;
M65 derivation 24, tenth stage.
-/

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace PoincareMT

/-- The actual open parameter disk has full measure in the closed disk.
Source: MT Lemma 19.2, p. 438; derivation 24, tenth stage. -/
theorem m65Ae_mem_openLoopDisk :
    ∀ᵐ z ∂volume.restrict loopDiskSet, z ∈ Metric.ball (0 : LoopPlane) 1 := by
  apply (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).mpr
  filter_upwards [compl_mem_ae_iff.2 (Measure.addHaar_sphere volume (0 : LoopPlane) 1)]
    with z hz
  intro hclosed
  change z ∈ loopDiskSet at hclosed
  rw [loopDiskSet, mem_closedBall_zero_iff] at hclosed
  rw [mem_ball_zero_iff]
  exact lt_of_le_of_ne hclosed (by simpa only [mem_compl_iff, Metric.mem_sphere,
    dist_zero_right] using hz)

/-- Genuine interior time derivatives and their continuous traces can be
integrated on the closed disk, using one common time neighborhood.
Source: MT Lemma 19.2, p. 438; derivation 24, tenth stage. -/
theorem m65HasDerivAt_integral_loopDisk_of_trace
    (f v : ℝ × LoopPlane → ℝ) {t δ : ℝ} (hδ : 0 < δ)
    (hf : ContinuousOn f (Metric.closedBall t δ ×ˢ loopDiskSet))
    (hv : ContinuousOn v (Metric.closedBall t δ ×ˢ loopDiskSet))
    (hderiv : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∀ s ∈ Metric.closedBall t δ,
      HasDerivAt (fun r => f (r, z)) (v (s, z)) s) :
    IntegrableOn (fun z => v (t, z)) loopDiskSet volume ∧
      HasDerivAt (fun s => ∫ z in loopDiskSet, f (s, z))
        (∫ z in loopDiskSet, v (t, z)) t := by
  have hcompact : IsCompact loopDiskSet := isCompact_closedBall (0 : LoopPlane) 1
  have hT : Metric.closedBall t δ ∈ 𝓝 t := Metric.closedBall_mem_nhds t hδ
  have htT : t ∈ Metric.closedBall t δ := Metric.mem_closedBall_self hδ.le
  have hslice (s : ℝ) (hs : s ∈ Metric.closedBall t δ) :
      ContinuousOn (fun z => f (s, z)) loopDiskSet :=
    hf.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨hs, hz⟩)
  have hvslice : ContinuousOn (fun z => v (t, z)) loopDiskSet :=
    hv.comp (continuousOn_const.prodMk continuousOn_id) (fun z hz => ⟨htT, hz⟩)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t δ).prod hcompact).exists_bound_of_continuousOn hv
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict loopDiskSet)
    (F := fun s z => f (s, z)) (F' := fun s z => v (s, z))
    (bound := fun _ => C) hT
  · filter_upwards [hT] with s hs
    exact (hslice s hs).aestronglyMeasurable Metric.isClosed_closedBall.measurableSet
  · exact (hslice t htT).integrableOn_compact hcompact
  · exact hvslice.aestronglyMeasurable Metric.isClosed_closedBall.measurableSet
  · filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
    intro s hs
    exact hC (s, z) ⟨hs, hz⟩
  · exact integrableOn_const hcompact.measure_ne_top
  · filter_upwards [m65Ae_mem_openLoopDisk] with z hz
    exact hderiv z hz

end PoincareMT
