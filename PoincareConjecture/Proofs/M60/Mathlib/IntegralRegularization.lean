import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic










set_option autoImplicit false

open Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M60

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f g : X → ℝ}




theorem tendsto_integral_regularized_ratio
    (hf : AEMeasurable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) (hg : Integrable g μ) :
    Tendsto (fun m : ℕ => ∫ x, (f x / (f x + 1 / ((m : ℝ) + 1))) * g x ∂μ)
      atTop (𝓝 (∫ x, g x ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖g x‖)
  · intro m
    exact ((hf.div (hf.add aemeasurable_const)).aestronglyMeasurable).mul
      hg.aestronglyMeasurable
  · exact hg.norm
  · intro m
    filter_upwards [hpos] with x hx
    have he : 0 < 1 / ((m : ℝ) + 1) := by positivity
    have hq0 : 0 ≤ f x / (f x + 1 / ((m : ℝ) + 1)) := by positivity
    have hq1 : f x / (f x + 1 / ((m : ℝ) + 1)) ≤ 1 :=
      (div_le_one (by positivity)).mpr (le_add_of_nonneg_right he.le)
    rw [norm_mul, Real.norm_of_nonneg hq0]
    exact mul_le_of_le_one_left (norm_nonneg _) hq1
  · filter_upwards [hpos] with x hx
    have hlim := (tendsto_const_nhds (x := f x)).div
      (tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat)
      (by simpa using hx.ne')
    simpa [hx.ne'] using hlim.mul_const (g x)




theorem measure_le_integral_of_regularized_ratios [IsFiniteMeasure μ]
    (hf : AEMeasurable f μ) (hpos : ∀ᵐ x ∂μ, 0 < f x) (hg : Integrable g μ)
    (hineq : ∀ ε : ℝ, 0 < ε →
      (∫ x, f x / (f x + ε) ∂μ) ≤ ∫ x, (f x / (f x + ε)) * g x ∂μ) :
    μ.real Set.univ ≤ ∫ x, g x ∂μ := by
  have hleft := tendsto_integral_regularized_ratio hf hpos (integrable_const (1 : ℝ))
  simp only [mul_one, integral_const, smul_eq_mul] at hleft
  apply le_of_tendsto_of_tendsto hleft (tendsto_integral_regularized_ratio hf hpos hg)
  exact Eventually.of_forall fun m => hineq _ (by positivity)




theorem log_regularization_inequality {a ε b c q : ℝ}
    (ha : 0 < a) (he : 0 < ε) (hq : 0 ≤ q)
    (hb : q / a + 2 * a - 2 * a * c ≤ b) :
    2 * a / (a + ε) - 2 * a * c / (a + ε) ≤
      b / (a + ε) - q / (a + ε) ^ 2 := by
  have hd : 0 < a + ε := add_pos ha he
  have hq' : q / (a + ε) ≤ q / a :=
    div_le_div_of_nonneg_left hq ha (le_add_of_nonneg_right he.le)
  have h : 2 * a - 2 * a * c ≤ b - q / (a + ε) := by linarith
  have hh := div_le_div_of_nonneg_right h hd.le
  simpa only [sub_div, div_div, pow_two] using hh

end PoincareConjecture.M60
