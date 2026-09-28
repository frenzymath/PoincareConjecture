import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Eventual
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.Analysis.Elliptic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]

theorem integral_abs_le_sqrt_integral_sq {f : X → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x) ^ 2 ∂μ) * Real.sqrt (μ.real univ) := by
  have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (by simpa using hf) (memLp_const (μ := μ) (1 : ℝ))
  simpa only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs,
    one_pow, integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] using h

theorem tendsto_integral_abs_of_integral_sq
    {f : ℕ → X → ℝ} (hf : ∀ᶠ k in atTop, MemLp (f k) 2 μ)
    (hlim : Tendsto (fun k => ∫ x, (f k x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |f k x| ∂μ) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun x => abs_nonneg _)
    (hf.mono fun k hk => integral_abs_le_sqrt_integral_sq hk)
  simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using
    (Real.continuous_sqrt.continuousAt.tendsto.comp hlim).mul_const (Real.sqrt (μ.real univ))

theorem abs_mul_sub_mul_le {a b c d L : ℝ}
    (hb : |b| ≤ L) (hc : |c| ≤ L) :
    |a * b - c * d| ≤ L * (|a - c| + |b - d|) := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by congr 1; ring
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ ≤ |a - c| * L + L * |b - d| := by
      simp only [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left hb (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hc (abs_nonneg _))
    _ = _ := by ring

theorem tendsto_integral_abs_mul_sub_of_integral_sq
    {f g : ℕ → X → ℝ} {f₀ g₀ : X → ℝ} {L : ℝ}
    (hf : ∀ᶠ k in atTop, MemLp (f k) 2 μ)
    (hg : ∀ᶠ k in atTop, MemLp (g k) 2 μ)
    (hf₀ : MemLp f₀ 2 μ) (hg₀ : MemLp g₀ 2 μ)
    (hgb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, |g k x| ≤ L)
    (hf₀b : ∀ᵐ x ∂μ, |f₀ x| ≤ L)
    (hflim : Tendsto (fun k => ∫ x, (f k x - f₀ x) ^ 2 ∂μ) atTop (𝓝 0))
    (hglim : Tendsto (fun k => ∫ x, (g k x - g₀ x) ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |f k x * g k x - f₀ x * g₀ x| ∂μ) atTop (𝓝 0) := by
  have hfL1 := tendsto_integral_abs_of_integral_sq (hf.mono fun k hk => hk.sub hf₀) hflim
  have hgL1 := tendsto_integral_abs_of_integral_sq (hg.mono fun k hk => hk.sub hg₀) hglim
  have hbound : ∀ᶠ k in atTop,
      (∫ x, |f k x * g k x - f₀ x * g₀ x| ∂μ) ≤
        L * ((∫ x, |f k x - f₀ x| ∂μ) + ∫ x, |g k x - g₀ x| ∂μ) := by
    filter_upwards [hf, hg, hgb] with k hkf hkg hkb
    have hfi : Integrable (fun x => |f k x - f₀ x|) μ :=
      ((hkf.sub hf₀).integrable (by norm_num)).norm
    have hgi : Integrable (fun x => |g k x - g₀ x|) μ :=
      ((hkg.sub hg₀).integrable (by norm_num)).norm
    have hprod : Integrable (fun x => |f k x * g k x - f₀ x * g₀ x|) μ :=
      ((hkf.integrable_mul hkg).sub (hf₀.integrable_mul hg₀)).norm
    calc
      _ ≤ ∫ x, L * (|f k x - f₀ x| + |g k x - g₀ x|) ∂μ := by
        apply integral_mono_ae hprod ((hfi.add hgi).const_mul L)
        filter_upwards [hkb, hf₀b] with x hx hx₀
        exact abs_mul_sub_mul_le hx hx₀
      _ = _ := by rw [integral_const_mul, integral_add hfi hgi]
  apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun x => abs_nonneg _)
    hbound
  simpa only [Pi.sub_apply, zero_add, mul_zero] using (hfL1.add hgL1).const_mul L

omit [IsFiniteMeasure μ] in
theorem tendsto_integral_abs_coefficient_mul_sub
    {A f : ℕ → X → ℝ} {A₀ f₀ : X → ℝ} {C : ℝ}
    (hA : ∀ᶠ k in atTop, AEStronglyMeasurable (A k) μ)
    (hA₀ : AEStronglyMeasurable A₀ μ)
    (hAb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, |A k x| ≤ C)
    (hA₀b : ∀ᵐ x ∂μ, |A₀ x| ≤ C)
    (hAlim : ∀ᵐ x ∂μ, Tendsto (fun k => A k x) atTop (𝓝 (A₀ x)))
    (hf : ∀ᶠ k in atTop, Integrable (f k) μ) (hf₀ : Integrable f₀ μ)
    (hflim : Tendsto (fun k => ∫ x, |f k x - f₀ x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, |A k x * f k x - A₀ x * f₀ x| ∂μ)
      atTop (𝓝 0) := by
  have hdiffb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, ‖A k x - A₀ x‖ ≤ 2 * C := by
    filter_upwards [hAb] with k hk
    filter_upwards [hk, hA₀b] with x hx hx₀
    simpa only [Real.norm_eq_abs, two_mul] using
      (abs_sub (A k x) (A₀ x)).trans (add_le_add hx hx₀)
  have hrem : Tendsto (fun k => ∫ x, |(A k x - A₀ x) * f₀ x| ∂μ)
      atTop (𝓝 0) := by
    have hm : ∀ᶠ k in atTop,
        AEStronglyMeasurable (fun x => |(A k x - A₀ x) * f₀ x|) μ := by
      filter_upwards [hA] with k hk
      simpa only [Real.norm_eq_abs, Pi.mul_apply, Pi.sub_apply] using
        ((hk.sub hA₀).mul hf₀.aestronglyMeasurable).norm
    have h := tendsto_integral_filter_of_dominated_convergence
      (fun x => 2 * C * |f₀ x|) hm
      (hdiffb.mono fun k hk => hk.mono fun x hx => by
        simpa only [Real.norm_eq_abs, abs_abs, abs_mul] using
          mul_le_mul_of_nonneg_right hx (abs_nonneg (f₀ x)))
      (hf₀.norm.const_mul (2 * C)) (by
        filter_upwards [hAlim] with x hx
        simpa only [sub_self, zero_mul, abs_zero] using
          (((hx.sub_const (A₀ x)).mul_const (f₀ x)).abs))
    simpa only [integral_zero] using h
  have hbound : ∀ᶠ k in atTop,
      (∫ x, |A k x * f k x - A₀ x * f₀ x| ∂μ) ≤
        C * (∫ x, |f k x - f₀ x| ∂μ) + ∫ x, |(A k x - A₀ x) * f₀ x| ∂μ := by
    filter_upwards [hA, hAb, hf, hdiffb] with k hkA hkb hkf hkdiff
    have hdiff : Integrable (fun x => |f k x - f₀ x|) μ := (hkf.sub hf₀).norm
    have hr : Integrable (fun x => |(A k x - A₀ x) * f₀ x|) μ :=
      (hf₀.bdd_mul (hkA.sub hA₀) hkdiff).norm
    have hi : Integrable (fun x => |A k x * f k x - A₀ x * f₀ x|) μ :=
      ((hkf.bdd_mul hkA (by simpa only [Real.norm_eq_abs] using hkb)).sub
        (hf₀.bdd_mul hA₀ (by simpa only [Real.norm_eq_abs] using hA₀b))).norm
    calc
      _ ≤ ∫ x, C * |f k x - f₀ x| + |(A k x - A₀ x) * f₀ x| ∂μ := by
        apply integral_mono_ae hi ((hdiff.const_mul C).add hr)
        filter_upwards [hkb] with x hx
        calc
          _ = |A k x * (f k x - f₀ x) + (A k x - A₀ x) * f₀ x| := by
            congr 1
            ring
          _ ≤ |A k x * (f k x - f₀ x)| + |(A k x - A₀ x) * f₀ x| :=
            abs_add_le _ _
          _ ≤ _ := by
            rw [abs_mul]
            exact add_le_add (mul_le_mul_of_nonneg_right hx (abs_nonneg _)) le_rfl
      _ = _ := by rw [integral_add (hdiff.const_mul C) hr, integral_const_mul]
  apply squeeze_zero' (Eventually.of_forall fun k => integral_nonneg fun x => abs_nonneg _)
    hbound
  simpa only [mul_zero, zero_add] using (hflim.const_mul C).add hrem

end Poincare.Analysis.Elliptic
