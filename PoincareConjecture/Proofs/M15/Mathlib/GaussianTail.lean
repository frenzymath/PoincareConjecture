import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace MeasureTheory

theorem setIntegral_exp_neg_le_half {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} {s : Set α} {a : ℝ}
    (hf : Measurable f) (hs : MeasurableSet s)
    (hint : Integrable (fun x => Real.exp (-f x / 2)) μ)
    (ha : ∀ x ∈ s, a ≤ f x) :
    IntegrableOn (fun x => Real.exp (-f x)) s μ ∧
      (∫ x in s, Real.exp (-f x) ∂μ) ≤
        Real.exp (-a / 2) * ∫ x, Real.exp (-f x / 2) ∂μ := by
  have hpoint (x : α) (hx : x ∈ s) :
      Real.exp (-f x) ≤ Real.exp (-a / 2) * Real.exp (-f x / 2) := by
    calc
      Real.exp (-f x) = Real.exp (-f x / 2) * Real.exp (-f x / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-a / 2) * Real.exp (-f x / 2) :=
        mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [ha x hx])) (Real.exp_pos _).le
  have hbig : IntegrableOn
      (fun x => Real.exp (-a / 2) * Real.exp (-f x / 2)) s μ :=
    (hint.const_mul _).integrableOn
  have hsmall : IntegrableOn (fun x => Real.exp (-f x)) s μ := by
    apply hbig.mono' hf.neg.exp.aestronglyMeasurable.restrict
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact hpoint x hx
  refine ⟨hsmall, ?_⟩
  calc
    (∫ x in s, Real.exp (-f x) ∂μ) ≤
        ∫ x in s, Real.exp (-a / 2) * Real.exp (-f x / 2) ∂μ :=
      setIntegral_mono_on hsmall hbig hs hpoint
    _ = Real.exp (-a / 2) * ∫ x in s, Real.exp (-f x / 2) ∂μ :=
      integral_const_mul _ _
    _ ≤ Real.exp (-a / 2) * ∫ x, Real.exp (-f x / 2) ∂μ :=
      mul_le_mul_of_nonneg_left
        (setIntegral_le_integral hint (Filter.Eventually.of_forall
          (fun x => (Real.exp_pos (-f x / 2)).le))) (Real.exp_pos _).le

theorem setIntegral_exp_neg_norm_sq_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {s : Set E} (hs : MeasurableSet s) {A : ℝ}
    (hA : 0 ≤ A) (haway : ∀ x ∈ s, A ≤ ‖x‖) :
    (∫ x in s, Real.exp (-‖x‖ ^ 2)) ≤
      Real.exp (-A ^ 2 / 2) *
        Real.rpow (2 * Real.pi) ((Module.finrank ℝ E : ℝ) / 2) := by
  have heval : (∫ x : E, Real.exp (-‖x‖ ^ 2 / 2)) =
      Real.rpow (2 * Real.pi) ((Module.finrank ℝ E : ℝ) / 2) := by
    have h := GaussianFourier.integral_rexp_neg_mul_sq_norm
      (V := E) (b := (1 / 2 : ℝ)) (by norm_num)
    convert h using 1
    · congr 1
      funext x
      congr 1
      ring
    · congr 1
      ring
  have hint : Integrable (fun x : E => Real.exp (-‖x‖ ^ 2 / 2)) := by
    by_contra h
    rw [integral_undef h] at heval
    exact (ne_of_gt (Real.rpow_pos_of_pos
      (mul_pos (by norm_num) Real.pi_pos) _)) heval.symm
  have htail := setIntegral_exp_neg_le_half (measurable_norm.pow_const 2) hs hint
    (fun x hx => pow_le_pow_left₀ hA (haway x hx) 2)
  rw [heval] at htail
  exact htail.2

end MeasureTheory

namespace Real

theorem exists_pos_exp_neg_div_le_rpow (C p : ℝ) {b : ℝ} (hb : 0 < b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      C * Real.exp (-b / ε) ≤ Real.rpow ε p := by
  have hlim : Tendsto
      (fun ε : ℝ => C * (Real.rpow ε⁻¹ p * Real.exp (-b * ε⁻¹)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero, Real.rpow_eq_pow] using tendsto_const_nhds.mul
      ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p b hb).comp
        tendsto_inv_nhdsGT_zero)
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      C * (Real.rpow ε⁻¹ p * Real.exp (-b * ε⁻¹)) < 1 :=
    hlim.eventually (gt_mem_nhds zero_lt_one)
  obtain ⟨η, hη, hbound⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hsmall
  change 0 < η at hη
  refine ⟨η / 2, by linarith, ?_⟩
  intro ε hε hεη
  have hlt : C * (Real.rpow ε⁻¹ p * Real.exp (-b * ε⁻¹)) < 1 :=
    hbound ⟨hε, by linarith⟩
  have hid : C * (Real.rpow ε⁻¹ p * Real.exp (-b * ε⁻¹)) =
      (C * Real.exp (-b / ε)) / Real.rpow ε p := by
    simp only [Real.rpow_eq_pow, Real.inv_rpow hε.le, div_eq_mul_inv]
    ring
  rw [hid] at hlt
  have h := (div_le_iff₀ (Real.rpow_pos_of_pos hε p)).mp hlt.le
  simpa only [one_mul, Real.rpow_eq_pow] using h

end Real
