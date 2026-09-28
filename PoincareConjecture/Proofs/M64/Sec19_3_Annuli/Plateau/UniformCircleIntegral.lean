import Mathlib.MeasureTheory.Integral.DominatedConvergence







set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in


theorem m64TendstoUniformlyOn_smul_bounded
    {X : Type*} {S : Set X} {f : ℕ → X → E} {u : X → E}
    (hlim : TendstoUniformlyOn f u atTop S) (b : X → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ x ∈ S, ‖b x‖ ≤ C) :
    TendstoUniformlyOn (fun j x => b x • f j x) (fun x => b x • u x) atTop S := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hCp : 0 < C + 1 := by linarith
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim
    (epsilon / (C + 1)) (div_pos hepsilon hCp)] with j hj
  intro x hx
  rw [dist_eq_norm, ← smul_sub, norm_smul]
  have hn := hj x hx
  rw [dist_eq_norm] at hn
  calc
    _ ≤ (C + 1) * ‖u x - f j x‖ :=
      mul_le_mul_of_nonneg_right ((hb x hx).trans (by linarith)) (norm_nonneg _)
    _ < (C + 1) * (epsilon / (C + 1)) := mul_lt_mul_of_pos_left hn hCp
    _ = epsilon := mul_div_cancel₀ _ hCp.ne'

omit [CompleteSpace E] in


theorem m64UniformCircle_weighted_integral_tendsto
    {f : ℕ → ℝ → E} {u : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ j, ContinuousOn (f j) (Icc a b))
    (hlim : TendstoUniformlyOn f u atTop (Icc a b))
    (w : ℝ → ℝ) (hw : ContinuousOn w (Icc a b)) :
    Tendsto (fun j => ∫ x in Icc a b, w x • f j x) atTop
      (𝓝 (∫ x in Icc a b, w x • u x)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  have huni := m64TendstoUniformlyOn_smul_bounded hlim w
    (le_max_left 0 C) (fun x hx => (hC x hx).trans (le_max_right 0 C))
  have hconv := TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    (μ := volume) (a := a) (b := b)
    (Eventually.of_forall (fun j => by simpa only [uIcc_of_le hab] using hw.smul (hf j)))
    (by simpa +instances only [uIcc_of_le hab, Pi.smul_apply] using! huni)
  simpa +instances only [intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc, Pi.smul_apply] using! hconv

end PoincareConjecture
