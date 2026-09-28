import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCollarFlux

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace

namespace PoincareConjecture.M65Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem interval_continuity_of_c1 {f : ℝ → E} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 f t) :
    ContinuousOn f (Icc a b) ∧ ContinuousOn (deriv f) (Icc a b) := by
  constructor
  · exact fun t ht => (hf t ht).continuousAt.continuousWithinAt
  · intro t ht
    have hh := ((hf t ht).fderiv_right (m := 0) (by norm_num)).continuousAt.clm_apply
      (continuousAt_const (x := t) (y := (1 : ℝ)))
    simpa only [fderiv_apply_one_eq_deriv] using hh.continuousWithinAt

private theorem interval_flux_integration_by_parts {T U N : ℝ → E} {a b : ℝ}
    (hab : a ≤ b)
    (hT : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 T t)
    (hU : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 U t)
    (hN : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 N t) :
    (∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) -
        (∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) =
      ⟪T b - U b, N b⟫_ℝ - ⟪T a - U a, N a⟫_ℝ -
        ∫ t in a..b, ⟪T t - U t, deriv N t⟫_ℝ := by
  let f := fun t => T t - U t
  have hf : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 f t := fun t ht => (hT t ht).sub (hU t ht)
  obtain ⟨hfc, hfdc⟩ := interval_continuity_of_c1 hf
  obtain ⟨hNc, hNdc⟩ := interval_continuity_of_c1 hN
  have hi1 := (hfc.inner (𝕜 := ℝ) hNdc).intervalIntegrable_of_Icc (μ := volume) hab
  have hi2 := (hfdc.inner (𝕜 := ℝ) hNc).intervalIntegrable_of_Icc (μ := volume) hab
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t ht =>
      ((hf t ((uIcc_of_le hab) ▸ ht)).differentiableAt one_ne_zero).hasDerivAt.inner ℝ
        ((hN t ((uIcc_of_le hab) ▸ ht)).differentiableAt one_ne_zero).hasDerivAt)
    (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hFTC
  have hiT := ((interval_continuity_of_c1 hT).2.inner (𝕜 := ℝ) hNc).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hiU := ((interval_continuity_of_c1 hU).2.inner (𝕜 := ℝ) hNc).intervalIntegrable_of_Icc
    (μ := volume) hab
  have hdiff : (∫ t in a..b, ⟪deriv f t, N t⟫_ℝ) =
      (∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) - (∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) := by
    rw [← intervalIntegral.integral_sub hiT hiU]
    apply intervalIntegral.integral_congr
    intro t ht
    have htc : t ∈ Icc a b := (uIcc_of_le hab) ▸ ht
    dsimp only
    rw [show deriv f t = deriv T t - deriv U t from
      deriv_sub ((hT t htc).differentiableAt one_ne_zero)
        ((hU t htc).differentiableAt one_ne_zero), inner_sub_left]
  dsimp only [f] at hFTC hdiff
  linarith only [hFTC, hdiff]

theorem collar_interval_flux_sq_bound {T U N : ℝ → E} {a b C L delta : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (_hL : 0 ≤ L) (hd : 0 ≤ delta)
    (hT : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 T t)
    (hU : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 U t)
    (hN : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 N t)
    (hclose : ∀ t ∈ Icc a b, ‖T t - U t‖ ≤ C * Real.sqrt delta)
    (hbound : ∀ t ∈ Icc a b, ‖N t‖ ≤ L) :
    ((∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) -
      ∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) ^ 2 ≤
        2 * C ^ 2 * delta * (4 * L ^ 2 + (b - a) * ∫ t in a..b, ‖deriv N t‖ ^ 2) := by
  let f := fun t => T t - U t
  let B := ⟪f b, N b⟫_ℝ - ⟪f a, N a⟫_ℝ
  let J := ∫ t in a..b, ⟪f t, deriv N t⟫_ℝ
  have hscale : 0 ≤ C * Real.sqrt delta := mul_nonneg hC (Real.sqrt_nonneg _)
  obtain ⟨hNc, hNdc⟩ := interval_continuity_of_c1 hN
  have hfc : ContinuousOn f (Icc a b) :=
    (interval_continuity_of_c1 hT).1.sub (interval_continuity_of_c1 hU).1
  have hendpoint (t : ℝ) (ht : t ∈ Icc a b) :
      |⟪f t, N t⟫_ℝ| ≤ C * Real.sqrt delta * L := by
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hclose t ht) (hbound t ht) (norm_nonneg _) hscale)
  have hBabs : |B| ≤ 2 * (C * Real.sqrt delta * L) := by
    calc
      _ ≤ |⟪f b, N b⟫_ℝ| + |⟪f a, N a⟫_ℝ| := by
        simpa only [Real.norm_eq_abs] using norm_sub_le ⟪f b, N b⟫_ℝ ⟪f a, N a⟫_ℝ
      _ ≤ _ := by linarith only [hendpoint b ⟨hab, le_rfl⟩, hendpoint a ⟨le_rfl, hab⟩]
  have hBsq : B ^ 2 ≤ 4 * C ^ 2 * delta * L ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg B) hBabs 2
    simp only [sq_abs, mul_pow, Real.sq_sqrt hd] at hh
    nlinarith only [hh]
  have hi : IntervalIntegrable (fun t => ‖deriv N t‖) volume a b :=
    hNdc.norm.intervalIntegrable_of_Icc hab
  have hi2 : IntervalIntegrable (fun t => ‖deriv N t‖ ^ 2) volume a b :=
    (hNdc.norm.pow 2).intervalIntegrable_of_Icc hab
  have hJabs : |J| ≤ (C * Real.sqrt delta) * ∫ t in a..b, ‖deriv N t‖ := by
    calc
      _ ≤ ∫ t in a..b, ‖⟪f t, deriv N t⟫_ℝ‖ := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm
            (f := fun t => ⟪f t, deriv N t⟫_ℝ) hab
      _ ≤ ∫ t in a..b, (C * Real.sqrt delta) * ‖deriv N t‖ := by
        apply intervalIntegral.integral_mono_on hab
          ((hfc.inner (𝕜 := ℝ) hNdc).norm.intervalIntegrable_of_Icc hab) (hi.const_mul _)
        intro t ht
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hclose t ht) (norm_nonneg _))
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hCS := intervalIntegral.integral_mul_weight_sq_le (f := fun t => ‖deriv N t‖)
    (w := fun _ => (1 : ℝ)) hab (fun _ => zero_le_one) intervalIntegrable_const
    (by simpa only [mul_one] using hi) (by simpa only [mul_one] using hi2)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at hCS
  have hJsq : J ^ 2 ≤ C ^ 2 * delta * (b - a) * ∫ t in a..b, ‖deriv N t‖ ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg J) hJabs 2
    simp only [sq_abs, mul_pow, Real.sq_sqrt hd] at hh
    have hboundCS := mul_le_mul_of_nonneg_left hCS (mul_nonneg (sq_nonneg C) hd)
    nlinarith only [hh, hboundCS]
  have heq := interval_flux_integration_by_parts hab hT hU hN
  change (∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) -
    (∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) = B - J at heq
  rw [heq]
  nlinarith only [hBsq, hJsq, sq_nonneg (B + J)]

private theorem interval_inner_uniform_error {u v w : ℝ → E} {a b K eta : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K)
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (hw : ContinuousOn w (Icc a b))
    (hub : ∀ t ∈ Icc a b, ‖u t‖ ≤ K)
    (he : ∀ t ∈ Icc a b, ‖v t - w t‖ ≤ eta) :
    ‖(∫ t in a..b, ⟪u t, v t⟫_ℝ) - ∫ t in a..b, ⟪u t, w t⟫_ℝ‖ ≤
      (b - a) * K * eta := by
  have hiV := (hu.inner (𝕜 := ℝ) hv).intervalIntegrable_of_Icc (μ := volume) hab
  have hiW := (hu.inner (𝕜 := ℝ) hw).intervalIntegrable_of_Icc (μ := volume) hab
  rw [← intervalIntegral.integral_sub hiV hiW]
  simp_rw [← inner_sub_right]
  calc
    _ ≤ ∫ t in a..b, ‖⟪u t, v t - w t⟫_ℝ‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _t in a..b, K * eta := by
      apply intervalIntegral.integral_mono_on hab
        ((hu.inner (𝕜 := ℝ) (hv.sub hw)).norm.intervalIntegrable_of_Icc hab)
        intervalIntegrable_const
      intro t ht
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hub t ht) (he t ht) (norm_nonneg _) hK)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

theorem collar_interval_flux_tendsto {T N : ℕ → ℝ → E} {U V : ℝ → E}
    {delta eta : ℕ → ℝ} {a b C L : ℝ}
    (hab : a ≤ b) (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hd : ∀ n, 0 ≤ delta n) (hdt : Tendsto delta atTop (𝓝 0))
    (hT : ∀ n, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (T n) t)
    (hN : ∀ n, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 (N n) t)
    (hU : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 U t) (hV : ContinuousOn V (Icc a b))
    (hclose : ∀ n, ∀ t ∈ Icc a b, ‖T n t - U t‖ ≤ C * Real.sqrt (delta n))
    (hbound : ∀ n, ∀ t ∈ Icc a b, ‖N n t‖ ≤ L)
    (hNclose : ∀ n, ∀ t ∈ Icc a b, ‖N n t - V t‖ ≤ eta n)
    (het : Tendsto eta atTop (𝓝 0))
    (henergy : Tendsto (fun n => delta n * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ t in a..b, ⟪deriv (T n) t, N n t⟫_ℝ) atTop
      (𝓝 (∫ t in a..b, ⟪deriv U t, V t⟫_ℝ)) := by
  let err := fun n => (∫ t in a..b, ⟪deriv (T n) t, N n t⟫_ℝ) -
    ∫ t in a..b, ⟪deriv U t, N n t⟫_ℝ
  have herr : Tendsto (fun n => err n ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => sq_nonneg (err n))
      (fun n => collar_interval_flux_sq_bound hab hC hL (hd n) (hT n) hU (hN n)
        (hclose n) (hbound n))
    have hh := (hdt.const_mul (8 * C ^ 2 * L ^ 2)).add
      (henergy.const_mul (2 * C ^ 2 * (b - a)))
    have heq : (fun n => 2 * C ^ 2 * delta n *
        (4 * L ^ 2 + (b - a) * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)) =
        (fun n => 8 * C ^ 2 * L ^ 2 * delta n +
          (2 * C ^ 2 * (b - a)) * (delta n * ∫ t in a..b, ‖deriv (N n) t‖ ^ 2)) := by
      funext n
      ring
    rw [heq]
    simpa only [mul_zero, zero_add] using hh
  have herr0 : Tendsto err atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp herr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hh
  have hUd := (interval_continuity_of_c1 hU).2
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hUd
  let K0 := max K 0
  have hK0 : 0 ≤ K0 := le_max_right _ _
  have hKb (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv U t‖ ≤ K0 :=
    (hK t ht).trans (le_max_left _ _)
  let errN := fun n => (∫ t in a..b, ⟪deriv U t, N n t⟫_ℝ) -
    ∫ t in a..b, ⟪deriv U t, V t⟫_ℝ
  have herrN : Tendsto errN atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg (errN n))
      (fun n => interval_inner_uniform_error hab hK0 hUd
        (interval_continuity_of_c1 (hN n)).1 hV hKb (hNclose n))
    simpa only [mul_zero] using het.const_mul ((b - a) * K0)
  have hh := herr0.add herrN
  simp only [err, errN, sub_add_sub_cancel, zero_add] at hh
  exact tendsto_sub_nhds_zero_iff.mp hh

end PoincareConjecture.M65Gauss
