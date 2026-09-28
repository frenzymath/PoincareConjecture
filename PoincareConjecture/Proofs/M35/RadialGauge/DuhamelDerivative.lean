import PoincareConjecture.Proofs.M35.RadialGauge.HeatDerivative
import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeGain
import Mathlib.Analysis.Calculus.ContDiff.Defs









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))


theorem heatAverage_time_stronglyMeasurable {f : ℝ → V → F}
    (hf : StronglyMeasurable (Function.uncurry f)) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s => heatAverage (t - s) (f s) x) := by
  have hi : StronglyMeasurable (fun p : ℝ × V =>
      f p.1 (x + Real.sqrt (2 * (t - p.1)) • p.2)) :=
    hf.comp_measurable (g := fun p : ℝ × V =>
      (p.1, x + Real.sqrt (2 * (t - p.1)) • p.2)) (by fun_prop)
  exact hi.integral_prod_right'



theorem heatGradientKernel_time_stronglyMeasurable {f : ℝ → V → F}
    (hf : StronglyMeasurable (Function.uncurry f)) (t : ℝ) (x : V) :
    StronglyMeasurable (fun s => heatGradientKernel (t - s) (f s) x) := by
  have hi : StronglyMeasurable (fun p : ℝ × V =>
      f p.1 (x + Real.sqrt (2 * (t - p.1)) • p.2)) :=
    hf.comp_measurable (g := fun p : ℝ × V =>
      (p.1, x + Real.sqrt (2 * (t - p.1)) • p.2)) (by fun_prop)
  have hz : StronglyMeasurable (fun p : ℝ × V => innerSL ℝ p.2) :=
    ((innerSL ℝ).continuous.comp continuous_snd).stronglyMeasurable
  have hk : StronglyMeasurable (fun p : ℝ × V => (innerSL ℝ p.2).smulRight
      (f p.1 (x + Real.sqrt (2 * (t - p.1)) • p.2))) :=
    (show Continuous (fun p : (V →L[ℝ] ℝ) × F => p.1.smulRight p.2) from
      ((ContinuousLinearMap.smulRightL ℝ V F).continuous.comp continuous_fst).clm_apply
        continuous_snd).comp_stronglyMeasurable (hz.prodMk hi)
  exact (show Measurable (fun s : ℝ => (Real.sqrt (2 * (t - s)))⁻¹) by
    fun_prop).stronglyMeasurable.smul hk.integral_prod_right'




theorem heatDuhamel_hasFDerivAt {f : ℝ → V → F} {f' : ℝ → V → V →L[ℝ] F}
    {C t : ℝ} (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hf' : ∀ s ∈ Ico 0 t, Continuous (f' s))
    (hderiv : ∀ s ∈ Ico 0 t, ∀ x, HasFDerivAt (f s) (f' s x) x)
    (hdbound : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x, ‖f' s x‖ ≤ D)
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    HasFDerivAt (heatDuhamel f t) (heatDuhamelGradient f t x) x := by
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (uIoc 0 t)) := by
    rw [uIoc_of_le ht]
    infer_instance
  let B (s : ℝ) := C * (gaussianFirstMoment (n + 1) * (t - s) ^ (-(1 / 2 : ℝ)) +
    gaussianSecondMoment (n + 1))
  have hB : IntervalIntegrable B volume 0 t :=
    (((intervalIntegrable_backwards_invSqrt t).const_mul (gaussianFirstMoment (n + 1))).add
      intervalIntegrable_const).const_mul C
  have hs : ∀ᵐ s ∂volume.restrict (uIoc 0 t), s ∈ Ico 0 t := by
    filter_upwards [ae_restrict_mem measurableSet_uIoc,
      (volume.restrict (uIoc 0 t)).ae_ne t] with s hs hne
    rw [uIoc_of_le ht] at hs
    exact ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
  unfold heatDuhamel heatDuhamelGradient
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le''
    (s := univ) (F' := fun y s => heatGradientKernel (t - s) (f s) y)
    (bound := B) (by simp)
  · exact Eventually.of_forall (fun y =>
      (heatAverage_time_stronglyMeasurable hfm t y).aestronglyMeasurable)
  · rw [intervalIntegrable_iff]
    apply (integrable_const C).mono'
      (heatAverage_time_stronglyMeasurable hfm t x).aestronglyMeasurable
    filter_upwards [hs] with s hs
    have hb (z : V) : ‖f s (x + Real.sqrt (2 * (t - s)) • z)‖ ≤ C := by
      have h := hbound s ⟨hs.1, hs.2.le⟩ (x + Real.sqrt (2 * (t - s)) • z)
      nlinarith [mul_nonneg (norm_nonneg (x + Real.sqrt (2 * (t - s)) • z))
        (norm_nonneg (f s (x + Real.sqrt (2 * (t - s)) • z)))]
    simpa [heatAverage] using
      norm_integral_le_of_norm_le_const (μ := stdGaussian V) (Eventually.of_forall hb)
  · exact (heatGradientKernel_time_stronglyMeasurable hfm t x).aestronglyMeasurable
  · filter_upwards [hs] with s hs y _
    have h := heatGradientKernel_weighted_norm_le_rpow
      (hf s ⟨hs.1, hs.2.le⟩) hC (hbound s ⟨hs.1, hs.2.le⟩) (sub_pos.mpr hs.2) y
    have hn := mul_nonneg (norm_nonneg y)
      (norm_nonneg (heatGradientKernel (t - s) (f s) y))
    dsimp only [B]
    nlinarith [h, hn]
  · exact hB
  · filter_upwards [hs] with s hs y _
    obtain ⟨D, hD⟩ := hdbound s hs
    exact heatAverage_hasFDerivAt (hf s ⟨hs.1, hs.2.le⟩) (hf' s hs)
      (hderiv s hs) (hbound s ⟨hs.1, hs.2.le⟩) hD (sub_pos.mpr hs.2) y



theorem heatDuhamel_fderiv_eq {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hfm : StronglyMeasurable (Function.uncurry f))
    (hf : ∀ s ∈ Icc 0 t, ContDiff ℝ 1 (f s))
    (hdbound : ∀ s ∈ Ico 0 t, ∃ D : ℝ, ∀ x, ‖fderiv ℝ (f s) x‖ ≤ D)
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    fderiv ℝ (heatDuhamel f t) x = heatDuhamelGradient f t x := by
  exact (heatDuhamel_hasFDerivAt hC ht hfm (fun s hs => (hf s hs).continuous)
    (fun s hs => (hf s ⟨hs.1, hs.2.le⟩).continuous_fderiv (by norm_num))
    (fun s hs x => ((hf s ⟨hs.1, hs.2.le⟩).differentiable (by norm_num) x).hasFDerivAt)
    hdbound hbound x).fderiv

end PoincareConjecture.M35.RadialGauge
