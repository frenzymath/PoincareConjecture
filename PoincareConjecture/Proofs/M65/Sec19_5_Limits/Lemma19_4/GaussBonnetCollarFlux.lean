import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetCollarLevels
import PoincareConjecture.Proofs.M65.Mathlib.WeightedCauchySchwarz
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology InnerProductSpace

namespace PoincareConjecture.M65Gauss

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private theorem periodic_inner_deriv_integral {f g : ℝ → E} {a b : ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hfp : f b = f a) (hgp : g b = g a) :
    (∫ t in a..b, ⟪deriv f t, g t⟫_ℝ) = -∫ t in a..b, ⟪f t, deriv g t⟫_ℝ := by
  have hi1 := (hf.continuous.inner (𝕜 := ℝ) hg.continuous_deriv_one).intervalIntegrable
    (μ := volume) a b
  have hi2 := (hf.continuous_deriv_one.inner (𝕜 := ℝ) hg.continuous).intervalIntegrable
    (μ := volume) a b
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b) (fun t _ =>
      (hf.differentiable one_ne_zero t).hasDerivAt.inner ℝ
        (hg.differentiable one_ne_zero t).hasDerivAt) (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2, hfp, hgp, sub_self] at hFTC
  linarith only [hFTC]




theorem collar_flux_sq_bound {T U N : ℝ → E} {a b C delta : ℝ}
    (hab : a ≤ b) (hd : 0 ≤ delta)
    (hT : ContDiff ℝ 1 T) (hU : ContDiff ℝ 1 U) (hN : ContDiff ℝ 1 N)
    (hTp : T b = T a) (hUp : U b = U a) (hNp : N b = N a)
    (hclose : ∀ t ∈ Icc a b, ‖T t - U t‖ ≤ C * Real.sqrt delta) :
    ((∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) -
      ∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) ^ 2 ≤
        C ^ 2 * delta * (b - a) * ∫ t in a..b, ‖deriv N t‖ ^ 2 := by
  let f := fun t => T t - U t
  have hf : ContDiff ℝ 1 f := hT.sub hU
  have hfp : f b = f a := by simp only [f, hTp, hUp]
  have hfd (t : ℝ) : deriv f t = deriv T t - deriv U t :=
    deriv_sub (hT.differentiable one_ne_zero t) (hU.differentiable one_ne_zero t)
  have hiT := (hT.continuous_deriv_one.inner (𝕜 := ℝ) hN.continuous).intervalIntegrable
    (μ := volume) a b
  have hiU := (hU.continuous_deriv_one.inner (𝕜 := ℝ) hN.continuous).intervalIntegrable
    (μ := volume) a b
  have heq : (∫ t in a..b, ⟪deriv T t, N t⟫_ℝ) -
      (∫ t in a..b, ⟪deriv U t, N t⟫_ℝ) =
        -∫ t in a..b, ⟪f t, deriv N t⟫_ℝ := by
    rw [← periodic_inner_deriv_integral hf hN hfp hNp]
    simp_rw [hfd, inner_sub_left]
    exact (intervalIntegral.integral_sub hiT hiU).symm
  have hc : Continuous (fun t => ‖deriv N t‖) := hN.continuous_deriv_one.norm
  have hi : IntervalIntegrable (fun t => ‖deriv N t‖) volume a b := hc.intervalIntegrable a b
  have hi2 : IntervalIntegrable (fun t => ‖deriv N t‖ ^ 2) volume a b :=
    (hc.pow 2).intervalIntegrable a b
  have hJ : 0 ≤ ∫ t in a..b, ‖deriv N t‖ :=
    intervalIntegral.integral_nonneg hab (fun t _ => norm_nonneg _)
  have hbound : |∫ t in a..b, ⟪f t, deriv N t⟫_ℝ| ≤
      (C * Real.sqrt delta) * ∫ t in a..b, ‖deriv N t‖ := by
    calc
      _ ≤ ∫ t in a..b, ‖⟪f t, deriv N t⟫_ℝ‖ := by
        simpa only [Real.norm_eq_abs] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun t => ⟪f t, deriv N t⟫_ℝ) hab
      _ ≤ ∫ t in a..b, (C * Real.sqrt delta) * ‖deriv N t‖ := by
        apply intervalIntegral.integral_mono_on hab
          ((hf.continuous.inner (𝕜 := ℝ) hN.continuous_deriv_one).norm.intervalIntegrable a b)
          (hi.const_mul _)
        intro t ht
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right (hclose t ht) (norm_nonneg _))
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hCS := intervalIntegral.integral_mul_weight_sq_le (f := fun t => ‖deriv N t‖)
    (w := fun _ => (1 : ℝ)) hab (fun _ => zero_le_one)
    (intervalIntegrable_const) (by simpa only [mul_one] using hi)
    (by simpa only [mul_one] using hi2)
  simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul] at hCS
  have hsq : (∫ t in a..b, ⟪f t, deriv N t⟫_ℝ) ^ 2 ≤
      (C * Real.sqrt delta) ^ 2 * (∫ t in a..b, ‖deriv N t‖) ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg (∫ t in a..b, ⟪f t, deriv N t⟫_ℝ)) hbound 2
    simpa only [sq_abs, mul_pow] using hh
  rw [heq, neg_sq]
  calc
    _ ≤ _ := hsq
    _ ≤ (C * Real.sqrt delta) ^ 2 *
        ((b - a) * ∫ t in a..b, ‖deriv N t‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hCS (sq_nonneg _)
    _ = _ := by rw [mul_pow, Real.sq_sqrt hd]; ring

private theorem integral_inner_uniform_error {u v w : ℝ → E} {a b K eta : ℝ}
    (hab : a ≤ b) (hK : 0 ≤ K) (hu : Continuous u) (hv : Continuous v) (hw : Continuous w)
    (hub : ∀ t ∈ Icc a b, ‖u t‖ ≤ K)
    (he : ∀ t ∈ Icc a b, ‖v t - w t‖ ≤ eta) :
    ‖(∫ t in a..b, ⟪u t, v t⟫_ℝ) - ∫ t in a..b, ⟪u t, w t⟫_ℝ‖ ≤
      (b - a) * K * eta := by
  have hiV := (hu.inner (𝕜 := ℝ) hv).intervalIntegrable (μ := volume) a b
  have hiW := (hu.inner (𝕜 := ℝ) hw).intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_sub hiV hiW]
  simp_rw [← inner_sub_right]
  calc
    _ ≤ ∫ t in a..b, ‖⟪u t, v t - w t⟫_ℝ‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ _t in a..b, K * eta := by
      apply intervalIntegral.integral_mono_on hab
        ((hu.inner (𝕜 := ℝ) (hv.sub hw)).norm.intervalIntegrable a b) intervalIntegrable_const
      intro t ht
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hub t ht) (he t ht) (norm_nonneg _) hK)
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring





theorem collar_flux_tendsto {T N : ℕ → ℝ → E} {U V : ℝ → E}
    {delta eta : ℕ → ℝ} {a b C : ℝ}
    (hab : a ≤ b) (hd : ∀ n, 0 ≤ delta n)
    (hT : ∀ n, ContDiff ℝ 1 (T n)) (hN : ∀ n, ContDiff ℝ 1 (N n))
    (hU : ContDiff ℝ 1 U) (hV : Continuous V)
    (hTp : ∀ n, T n b = T n a) (hNp : ∀ n, N n b = N n a) (hUp : U b = U a)
    (hclose : ∀ n, ∀ t ∈ Icc a b, ‖T n t - U t‖ ≤ C * Real.sqrt (delta n))
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
      (fun n => collar_flux_sq_bound hab (hd n) (hT n) hU (hN n)
        (hTp n) hUp (hNp n) (hclose n))
    have hh := henergy.const_mul (C ^ 2 * (b - a))
    convert hh using 1 <;> simp only [mul_zero, mul_assoc, mul_left_comm, mul_comm]
  have herr0 : Tendsto err atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp herr
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs] using hh
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hU.continuous_deriv_one.continuousOn
  let K0 := max K 0
  have hK0 : 0 ≤ K0 := le_max_right _ _
  have hKb (t : ℝ) (ht : t ∈ Icc a b) : ‖deriv U t‖ ≤ K0 :=
    (hK t ht).trans (le_max_left _ _)
  let errN := fun n => (∫ t in a..b, ⟪deriv U t, N n t⟫_ℝ) -
    ∫ t in a..b, ⟪deriv U t, V t⟫_ℝ
  have herrN : Tendsto errN atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    apply squeeze_zero (fun n => norm_nonneg (errN n))
      (fun n => integral_inner_uniform_error hab hK0 hU.continuous_deriv_one
        (hN n).continuous hV hKb (hNclose n))
    simpa only [mul_zero] using het.const_mul ((b - a) * K0)
  have hh := herr0.add herrN
  simp only [err, errN, sub_add_sub_cancel, zero_add] at hh
  exact (tendsto_sub_nhds_zero_iff).mp hh

end PoincareConjecture.M65Gauss
