import PoincareConjecture.Proofs.M35.RadialGauge.HeatTimeLipschitz
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace PoincareConjecture.M35.RadialGauge

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem moving_time_integral_hasDerivAt {H : ℝ → ℝ → F} {A : ℝ → F}
    {K : ℝ≥0} {t : ℝ} (ht : 0 ≤ t)
    (hm : ∀ a, StronglyMeasurable (H a))
    (hi : ∀ a b c, IntervalIntegrable (H a) volume b c)
    (hAm : StronglyMeasurable A)
    (hL : ∀ s, LipschitzWith K (fun a => H a s))
    (hd : ∀ s ∈ Ico 0 t, HasDerivAt (fun a => H a s) (A s) t)
    (hc : ContinuousAt (H t) t) :
    HasDerivAt (fun a => ∫ s in (0 : ℝ)..a, H a s)
      ((∫ s in (0 : ℝ)..t, A s) + H t t) t := by
  let base (a : ℝ) := ∫ s in (0 : ℝ)..t, H a s
  let prim (a : ℝ) := ∫ s in t..a, H t s
  let err (a : ℝ) := ∫ s in t..a, H a s - H t s
  let : IsFiniteMeasure ((volume : Measure ℝ).restrict (Ioc 0 t)) := inferInstance
  have hs : ∀ᵐ s ∂volume.restrict (Ioc 0 t), s ∈ Ico 0 t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,
      (volume.restrict (Ioc 0 t)).ae_ne t] with s hs hne
    exact ⟨hs.1.le, lt_of_le_of_ne hs.2 hne⟩
  have hb : HasDerivAt base (∫ s in (0 : ℝ)..t, A s) t := by
    have h := hasDerivAt_integral_of_dominated_loc_of_lip
      (μ := volume.restrict (Ioc 0 t)) (s := univ) (F := H) (F' := A)
      (bound := fun _ => (K : ℝ)) (by simp)
      (Eventually.of_forall (fun a => (hm a).aestronglyMeasurable)) (hi t 0 t).1
      hAm.aestronglyMeasurable
      (Eventually.of_forall (fun s => by simpa using hL s))
      (integrable_const (K : ℝ)) (hs.mono (fun s hs' => hd s hs'))
    simpa only [base, intervalIntegral.integral_of_le ht] using h.2
  have hp : HasDerivAt prim (H t t) t :=
    intervalIntegral.integral_hasDerivAt_right (hi t t t) (hm t).stronglyMeasurableAtFilter hc
  have he (a : ℝ) : ‖err a‖ ≤ (K : ℝ) * ‖a - t‖ ^ 2 := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := t) (b := a) (f := fun s => H a s - H t s) (C := (K : ℝ) * ‖a - t‖)
      (fun s _ => by simpa only [dist_eq_norm] using (hL s).dist_le_mul a t)
    simpa only [err, Real.norm_eq_abs, pow_two, mul_assoc] using h
  have he0 : HasDerivAt err 0 t := by
    apply hasDerivAt_iff_tendsto.mpr
    have het : err t = 0 := by simp only [err, intervalIntegral.integral_same]
    simp only [het, sub_zero, smul_zero]
    have hlim : Tendsto (fun a : ℝ => (K : ℝ) * ‖a - t‖) (𝓝 t) (𝓝 0) := by
      simpa using (((tendsto_id : Tendsto (fun a : ℝ => a) (𝓝 t) (𝓝 t)).sub_const t).norm.const_mul
        (K : ℝ))
    apply squeeze_zero (fun a => mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))
      (fun a => ?_) hlim
    by_cases hat : a = t
    · subst a
      simp
    have hn : ‖a - t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hat)
    calc
      _ ≤ ‖a - t‖⁻¹ * ((K : ℝ) * ‖a - t‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (he a) (inv_nonneg.mpr (norm_nonneg _))
      _ = _ := by field_simp [hn]
  have heq : (fun a => ∫ s in (0 : ℝ)..a, H a s) = fun a => base a + prim a + err a := by
    funext a
    dsimp only [base, prim, err]
    rw [intervalIntegral.integral_sub (hi a t a) (hi t t a),
      ← intervalIntegral.integral_add_adjacent_intervals (hi a 0 t) (hi a t a)]
    abel
  rw [heq]
  convert! (hb.add hp).add he0 using 1
  simp

end PoincareConjecture.M35.RadialGauge
