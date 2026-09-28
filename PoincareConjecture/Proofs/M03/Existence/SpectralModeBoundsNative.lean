import PoincareConjecture.Proofs.M03.Existence.SpectralModeNative









set_option autoImplicit false

open MeasureTheory Set

noncomputable section

namespace PoincareConjecture


theorem intervalIntegral_sq_le_time_mul_integral_sq
    {T : ℝ} {f : ℝ → ℝ} (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, f t) ^ 2 ≤ T * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  rcases eq_or_lt_of_le hT with hzero | hpos
  · subst T
    simp
  let I : ℝ := ∫ t in (0 : ℝ)..T, f t
  have hi : IntervalIntegrable f volume 0 T := hf.intervalIntegrable_of_Icc hT
  have hi2 : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    (hf.pow 2).intervalIntegrable_of_Icc hT
  have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..T, (T * f t - I) ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hT (fun _ => sq_nonneg _)
  have hexpand : (∫ t in (0 : ℝ)..T, (T * f t - I) ^ 2) =
      T ^ 2 * (∫ t in (0 : ℝ)..T, f t ^ 2) - 2 * T * I * I + T * I ^ 2 := by
    calc
      _ = ∫ t in (0 : ℝ)..T, T ^ 2 * f t ^ 2 - (2 * T * I) * f t + I ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t ht
        ring
      _ = _ := by
        rw [intervalIntegral.integral_add
          ((hi2.const_mul (T ^ 2)).sub (hi.const_mul (2 * T * I)))
          intervalIntegrable_const,
          intervalIntegral.integral_sub (hi2.const_mul (T ^ 2))
            (hi.const_mul (2 * T * I)),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        rfl
  have hmul : 0 ≤ T * (T * (∫ t in (0 : ℝ)..T, f t ^ 2) - I ^ 2) := by
    rw [hexpand] at hnonneg
    nlinarith
  have hdiff := nonneg_of_mul_nonneg_right hmul hpos
  exact sub_nonneg.mp hdiff


theorem spectralMode_zero_initial_normSq_le_time_integral
    {lambda T t : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) (ht : t ∈ Icc (0 : ℝ) T) :
    spectralMode lambda 0 f t ^ 2 ≤ t * ∫ s in (0 : ℝ)..t, f s ^ 2 := by
  let q : ℝ → ℝ := fun s => Real.exp (-lambda * (t - s)) * f s
  have hft : ContinuousOn f (Icc (0 : ℝ) t) :=
    hf.mono (Icc_subset_Icc le_rfl ht.2)
  have he : Continuous (fun s : ℝ => Real.exp (-lambda * (t - s))) := by fun_prop
  have hq : ContinuousOn q (Icc (0 : ℝ) t) := he.continuousOn.mul hft
  have hq2 : ∀ s ∈ Icc (0 : ℝ) t, q s ^ 2 ≤ f s ^ 2 := by
    intro s hs
    have hexp0 : 0 ≤ Real.exp (-lambda * (t - s)) := (Real.exp_pos _).le
    have hexp1 : Real.exp (-lambda * (t - s)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hlambda) (sub_nonneg.mpr hs.2)
    have hsquare : Real.exp (-lambda * (t - s)) ^ 2 ≤ 1 := by nlinarith
    calc
      q s ^ 2 = Real.exp (-lambda * (t - s)) ^ 2 * f s ^ 2 := by
        simp only [q, mul_pow]
      _ ≤ 1 * f s ^ 2 := mul_le_mul_of_nonneg_right hsquare (sq_nonneg _)
      _ = f s ^ 2 := one_mul _
  have hqint : IntervalIntegrable (fun s => q s ^ 2) volume 0 t :=
    (hq.pow 2).intervalIntegrable_of_Icc ht.1
  have hfint : IntervalIntegrable (fun s => f s ^ 2) volume 0 t :=
    (hft.pow 2).intervalIntegrable_of_Icc ht.1
  have hmono := intervalIntegral.integral_mono_on ht.1 hqint hfint hq2
  have hsq := intervalIntegral_sq_le_time_mul_integral_sq ht.1 hq
  have hmode : spectralMode lambda 0 f t = ∫ s in (0 : ℝ)..t, q s := by
    rw [spectralMode_eq_convolution]
    simp [q]
  rw [hmode]
  exact hsq.trans (mul_le_mul_of_nonneg_left hmono ht.1)


theorem spectralMode_zero_initial_energy_le_time_sq
    {lambda T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, spectralMode lambda 0 f t ^ 2) ≤
      T ^ 2 * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have hfint : IntervalIntegrable (fun t => f t ^ 2) volume 0 T :=
    (hf.pow 2).intervalIntegrable_of_Icc hT
  have hpoint : ∀ t ∈ Icc (0 : ℝ) T,
      spectralMode lambda 0 f t ^ 2 ≤ T * ∫ s in (0 : ℝ)..T, f s ^ 2 := by
    intro t ht
    have htrace := spectralMode_zero_initial_normSq_le_time_integral hlambda hf ht
    have hmono := intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall (fun s => sq_nonneg (f s))) hfint
    have hprefix : 0 ≤ ∫ s in (0 : ℝ)..t, f s ^ 2 :=
      intervalIntegral.integral_nonneg_of_forall ht.1 (fun _ => sq_nonneg _)
    exact htrace.trans (mul_le_mul ht.2 hmono hprefix hT)
  have hu := continuousOn_spectralMode (lambda := lambda) (c := 0) hf
  have hint : IntervalIntegrable
      (fun t => spectralMode lambda 0 f t ^ 2) volume 0 T :=
    (hu.pow 2).intervalIntegrable_of_Icc hT
  calc
    _ ≤ ∫ _t in (0 : ℝ)..T, T * ∫ s in (0 : ℝ)..T, f s ^ 2 :=
      intervalIntegral.integral_mono_on hT hint intervalIntegrable_const hpoint
    _ = _ := by
      rw [intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul]
      ring


theorem spectralMode_zero_initial_shifted_energy_le
    {lambda T : ℝ} {f : ℝ → ℝ} (hlambda : 0 ≤ lambda) (hT : 0 ≤ T)
    (hf : ContinuousOn f (Icc (0 : ℝ) T)) :
    (∫ t in (0 : ℝ)..T, (1 + lambda) * spectralMode lambda 0 f t ^ 2) ≤
      (T + T ^ 2) * ∫ t in (0 : ℝ)..T, f t ^ 2 := by
  have hlow := spectralMode_zero_initial_energy_le_time_sq hlambda hT hf
  have hmid := spectralMode_zero_initial_intermediate_energy_le hlambda hT hf
  have hu := continuousOn_spectralMode (lambda := lambda) (c := 0) hf
  have hi : IntervalIntegrable (fun t => spectralMode lambda 0 f t ^ 2) volume 0 T :=
    (hu.pow 2).intervalIntegrable_of_Icc hT
  have hsplit : (∫ t in (0 : ℝ)..T, (1 + lambda) * spectralMode lambda 0 f t ^ 2) =
      (∫ t in (0 : ℝ)..T, spectralMode lambda 0 f t ^ 2) +
      (∫ t in (0 : ℝ)..T, lambda * spectralMode lambda 0 f t ^ 2) := by
    rw [← intervalIntegral.integral_add hi (hi.const_mul lambda)]
    apply intervalIntegral.integral_congr
    intro t ht
    ring
  rw [hsplit]
  nlinarith


theorem spectralMode_sub
    {lambda c d T t : ℝ} {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Icc (0 : ℝ) T))
    (hg : ContinuousOn g (Icc (0 : ℝ) T)) (ht : t ∈ Icc (0 : ℝ) T) :
    spectralMode lambda c f t - spectralMode lambda d g t =
      spectralMode lambda (c - d) (fun s => f s - g s) t := by
  have he : Continuous (fun s : ℝ => Real.exp (lambda * s)) := by fun_prop
  have hF : IntervalIntegrable (fun s => Real.exp (lambda * s) * f s) volume 0 t :=
    (he.continuousOn.mul (hf.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  have hG : IntervalIntegrable (fun s => Real.exp (lambda * s) * g s) volume 0 t :=
    (he.continuousOn.mul (hg.mono (Icc_subset_Icc le_rfl ht.2))).intervalIntegrable_of_Icc ht.1
  simp only [spectralMode, mul_sub]
  rw [intervalIntegral.integral_sub hF hG]
  ring

end PoincareConjecture
