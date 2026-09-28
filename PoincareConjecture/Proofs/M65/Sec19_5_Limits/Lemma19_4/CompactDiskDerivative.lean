import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.EnergyVariation
import Mathlib.Analysis.Calculus.ParametricIntegral










set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology ContDiff

namespace PoincareConjecture




theorem m65HasDerivAt_integral_loopDisk
    (f : ℝ × LoopPlane → ℝ) {t : ℝ}
    (hf : ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 f (t, z)) :
    IntegrableOn (fun z => fderiv ℝ f (t, z) (1, 0)) loopDiskSet volume ∧
      HasDerivAt (fun s => ∫ z in loopDiskSet, f (s, z))
        (∫ z in loopDiskSet, fderiv ℝ f (t, z) (1, 0)) t := by
  have hcompact : IsCompact loopDiskSet := isCompact_closedBall (0 : LoopPlane) 1
  have hnear : ∀ᶠ s in 𝓝 t, ∀ z ∈ loopDiskSet, ContDiffAt ℝ 1 f (s, z) :=
    hcompact.eventually_forall_of_forall_eventually
      (fun z hz => (hf z hz).eventually (by simp))
  obtain ⟨δ, hδ, hδU⟩ := Metric.nhds_basis_closedBall.mem_iff.mp hnear
  let T := Metric.closedBall t δ
  let K : Set (ℝ × LoopPlane) := T ×ˢ loopDiskSet
  have hT : T ∈ 𝓝 t := Metric.closedBall_mem_nhds t hδ
  have htT : t ∈ T := Metric.mem_closedBall_self hδ.le
  have hreg (s : ℝ) (hs : s ∈ T) (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      ContDiffAt ℝ 1 f (s, z) := hδU hs z hz
  have hpartial : ContinuousOn (fun p : ℝ × LoopPlane => fderiv ℝ f p (1, 0)) K := by
    intro p hp
    exact (((hreg p.1 hp.1 p.2 hp.2).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).continuousWithinAt
  obtain ⟨C, hC⟩ := ((isCompact_closedBall t δ).prod hcompact).exists_bound_of_continuousOn
    hpartial
  have hcont (s : ℝ) (hs : s ∈ T) : ContinuousOn (fun z => f (s, z)) loopDiskSet := by
    intro z hz
    exact ((hreg s hs z hz).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hcont' : ContinuousOn (fun z => fderiv ℝ f (t, z) (1, 0)) loopDiskSet := by
    intro z hz
    exact ((((hreg t htT z hz).continuousAt_fderiv (by simp)).clm_apply
      continuousAt_const).comp
        (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict loopDiskSet)
    (F := fun s z => f (s, z)) (F' := fun s z => fderiv ℝ f (s, z) (1, 0))
    (bound := fun _ => C) hT
  · filter_upwards [hT] with s hs
    exact (hcont s hs).aestronglyMeasurable Metric.isClosed_closedBall.measurableSet
  · exact (hcont t htT).integrableOn_compact hcompact
  · exact hcont'.aestronglyMeasurable Metric.isClosed_closedBall.measurableSet
  · filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
    intro s hs
    exact hC (s, z) ⟨hs, hz⟩
  · exact integrableOn_const hcompact.measure_ne_top
  · filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet] with z hz
    intro s hs
    have h := ((hreg s hs z hz).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk (hasDerivAt_const s z))
    simpa +instances only [Function.comp_def, id_eq] using! h

end PoincareConjecture
