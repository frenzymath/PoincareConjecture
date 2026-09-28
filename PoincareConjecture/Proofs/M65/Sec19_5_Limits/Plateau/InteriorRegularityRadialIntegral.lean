import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPolarMeasure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal

namespace PoincareConjecture.M65Interior

theorem polar_integrable_weighted {f : LoopPlane → ℝ} (hf : Integrable f)
    (x : LoopPlane) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * f (polarPlane x p)) polarCoord.target := by
  have hi := (polarPlane_measurePreserving x).integrable_comp_of_integrable hf
  rw [polarMeasure, integrable_withDensity_iff_integrable_smul'
    (measurable_fst.ennreal_ofReal) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hi
  apply hi.congr
  filter_upwards [ae_restrict_mem polarCoord.open_target.measurableSet] with p hp
  simp only [ENNReal.toReal_ofReal hp.1.le, smul_eq_mul, Function.comp_apply]

private theorem integral_centered_polar {f : LoopPlane → ℝ} (x : LoopPlane) :
    (∫ p in polarCoord.target, p.1 * f (polarPlane x p)) = ∫ z, f z := by
  have h := Proofs.M58.integral_polar_loopPlane (fun z => f (x + z))
  change (∫ p in polarCoord.target, p.1 * f (x + p.1 • Proofs.M58.angularPoint p.2)) = _
  rw [h]
  exact (measurePreserving_add_left volume x).integral_comp
    (Homeomorph.addLeft x).measurableEmbedding f

theorem disk_integral_polar (f : LoopPlane → ℝ) (x : LoopPlane) (R : ℝ) :
    (∫ z in Metric.closedBall x R, f z) =
      ∫ p in Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 * f (polarPlane x p) := by
  classical
  let S : Set (ℝ × ℝ) := Iic R ×ˢ univ
  have hS : MeasurableSet S := measurableSet_Iic.prod MeasurableSet.univ
  have hset : S ∩ polarCoord.target = Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi := by
    ext p
    simp only [S, polarCoord_target, mem_inter_iff, mem_prod, mem_Iic, mem_univ,
      and_true, mem_Ioi, mem_Ioc, mem_Ioo]
    tauto
  rw [← integral_indicator (s := Metric.closedBall x R)
    Metric.isClosed_closedBall.measurableSet, ← integral_centered_polar x]
  calc
    _ = ∫ p in polarCoord.target,
        S.indicator (fun p => p.1 * f (polarPlane x p)) p := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet
      intro p hp
      have hr : 0 < p.1 := hp.1
      have hdist : dist (polarPlane x p) x = p.1 := by
        rw [dist_eq_norm]
        simp only [polarPlane, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
          abs_of_pos hr, Proofs.M58.norm_angularPoint, mul_one]
      have hm : polarPlane x p ∈ Metric.closedBall x R ↔ p ∈ S := by
        simp only [Metric.mem_closedBall, hdist, S, mem_prod, mem_Iic, mem_univ, and_true]
      dsimp only
      by_cases h : p ∈ S
      · erw [indicator_of_mem (hm.mpr h), indicator_of_mem h]
      · erw [indicator_of_notMem (mt hm.mp h), indicator_of_notMem h, mul_zero]
    _ = _ := by rw [integral_indicator hS, Measure.restrict_restrict hS, hset]

theorem disk_integral_radial {f : LoopPlane → ℝ} (hf : Integrable f)
    (x : LoopPlane) {R : ℝ} (hR : 0 ≤ R) :
    IntervalIntegrable (fun r => r * ∫ θ in Ioo (-Real.pi) Real.pi,
      f (polarPlane x (r, θ))) volume 0 R ∧
    (∫ z in Metric.closedBall x R, f z) =
      ∫ r in (0 : ℝ)..R, r * ∫ θ in Ioo (-Real.pi) Real.pi,
        f (polarPlane x (r, θ)) := by
  have hi := (polar_integrable_weighted hf x).mono_set
    (show Ioc (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi ⊆ polarCoord.target from
      fun _ hp => ⟨hp.1.1, hp.2⟩)
  have hip : Integrable (fun p : ℝ × ℝ => p.1 * f (polarPlane x p))
      ((volume.restrict (Ioc (0 : ℝ) R)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rwa [Measure.prod_restrict]
  have hj := hip.integral_prod_left
  simp only [integral_const_mul] at hj
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le hR).mpr hj, ?_⟩
  rw [disk_integral_polar, intervalIntegral.integral_of_le hR]
  have heq := integral_prod _ hip
  rw [Measure.prod_restrict] at heq
  simpa only [← Measure.volume_eq_prod, integral_const_mul] using heq

private theorem absolutelyContinuous_congr {f g : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) (heq : EqOn f g (uIcc a b)) :
    AbsolutelyContinuousOnInterval g a b := by
  rw [absolutelyContinuousOnInterval_iff] at hf ⊢
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := hf ε hε
  refine ⟨δ, hδ, fun E hE hlen => ?_⟩
  have hsum : (∑ i ∈ Finset.range E.1, dist (f (E.2 i).1) (f (E.2 i).2)) =
      ∑ i ∈ Finset.range E.1, dist (g (E.2 i).1) (g (E.2 i).2) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [heq (hE.1 i hi).1, heq (hE.1 i hi).2]
  rw [← hsum]
  exact hbound E hE hlen

theorem disk_integral_absolutelyContinuous {f : LoopPlane → ℝ} (hf : Integrable f)
    (x : LoopPlane) {R : ℝ} (hR : 0 ≤ R) :
    AbsolutelyContinuousOnInterval (fun s => ∫ z in Metric.closedBall x s, f z) 0 R := by
  apply absolutelyContinuous_congr
    ((disk_integral_radial hf x hR).1.absolutelyContinuousOnInterval_intervalIntegral
      (c := 0) (by simp [hR]))
  intro s hs
  have hs' : 0 ≤ s := (uIcc_of_le hR ▸ hs).1
  exact (disk_integral_radial hf x hs').2.symm

theorem disk_integral_ae_hasDerivAt {f : LoopPlane → ℝ} (hf : Integrable f)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R) :
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      HasDerivAt (fun s => ∫ z in Metric.closedBall x s, f z)
        (r * ∫ θ in Ioo (-Real.pi) Real.pi, f (polarPlane x (r, θ))) r := by
  have hj := (disk_integral_radial hf x hR.le).1
  filter_upwards [ae_restrict_of_ae hj.ae_hasDerivAt_integral,
    ae_restrict_mem measurableSet_Ioo] with r hr hrmem
  have hd := hr (by simpa only [uIcc_of_le hR.le] using
    (show r ∈ Icc (0 : ℝ) R from ⟨hrmem.1.le, hrmem.2.le⟩))
    (0 : ℝ) (by simp [hR.le])
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hrmem.1] with s hs
  exact (disk_integral_radial hf x hs.le).2

theorem local_disk_radial {f : LoopPlane → ℝ} {x : LoopPlane} {R : ℝ}
    (hR : 0 < R) (hf : IntegrableOn f (Metric.closedBall x R)) :
    AbsolutelyContinuousOnInterval (fun s => ∫ z in Metric.closedBall x s, f z) 0 R ∧
    ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) R),
      IntegrableOn (fun θ => f (polarPlane x (r, θ))) (Ioo (-Real.pi) Real.pi) ∧
      HasDerivAt (fun s => ∫ z in Metric.closedBall x s, f z)
        (r * ∫ θ in Ioo (-Real.pi) Real.pi, f (polarPlane x (r, θ))) r := by
  classical
  let g := (Metric.closedBall x R).indicator f
  have hg : Integrable g :=
    (integrable_indicator_iff Metric.isClosed_closedBall.measurableSet).mpr hf
  have hdisk (s : ℝ) (hs : s ≤ R) :
      (∫ z in Metric.closedBall x s, g z) = ∫ z in Metric.closedBall x s, f z := by
    apply setIntegral_congr_fun Metric.isClosed_closedBall.measurableSet
    intro z hz
    exact indicator_of_mem (Metric.closedBall_subset_closedBall hs hz) f
  have hcircle (r : ℝ) (hr : 0 ≤ r) (hrR : r ≤ R) (θ : ℝ) :
      g (polarPlane x (r, θ)) = f (polarPlane x (r, θ)) := by
    apply indicator_of_mem
    rw [Metric.mem_closedBall, dist_eq_norm]
    simpa only [polarPlane, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg hr, Proofs.M58.norm_angularPoint, mul_one] using hrR
  have hip : Integrable (fun p : ℝ × ℝ => p.1 * g (polarPlane x p))
      ((volume.restrict (Ioo (0 : ℝ) R)).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (polar_integrable_weighted hg x).mono_set (fun _ hp => ⟨hp.1.1, hp.2⟩)
  refine ⟨?_, ?_⟩
  · apply absolutelyContinuous_congr (disk_integral_absolutelyContinuous hg x hR.le)
    intro s hs
    exact hdisk s (uIcc_of_le hR.le ▸ hs).2
  filter_upwards [disk_integral_ae_hasDerivAt hg x hR, hip.prod_right_ae,
    ae_restrict_mem measurableSet_Ioo] with r hd hi hr
  have heq : (fun θ => g (polarPlane x (r, θ))) =
      fun θ => f (polarPlane x (r, θ)) := funext (hcircle r hr.1.le hr.2.le)
  have hci : IntegrableOn (fun θ => g (polarPlane x (r, θ)))
      (Ioo (-Real.pi) Real.pi) := by
    have hc := hi.const_mul r⁻¹
    simpa only [IntegrableOn, ← mul_assoc, inv_mul_cancel₀ hr.1.ne', one_mul] using hc
  refine ⟨heq ▸ hci, ?_⟩
  rw [heq] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hr.2] with s hs
  exact (hdisk s hs.le).symm

end PoincareConjecture.M65Interior
