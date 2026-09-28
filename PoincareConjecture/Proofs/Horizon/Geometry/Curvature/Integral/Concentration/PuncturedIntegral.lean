import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped Topology

namespace Poincare.CurvatureIntegral

theorem integral_le_of_compl_ball_bounds
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    {μ : Measure X} [NullSingletonClass μ] {E : Set X}
    (hE : MeasurableSet E) {h : X → ℝ} (hi : IntegrableOn h E μ)
    (p : X) {C : ℝ}
    (hbound : ∀ a : ℝ, 0 < a → (∫ x in E \ Metric.ball p a, h x ∂μ) ≤ C) :
    (∫ x in E, h x ∂μ) ≤ C := by
  let S : ℕ → Set X := fun j => E \ Metric.ball p ((1 / 2 : ℝ) ^ j)
  have hSm (j : ℕ) : MeasurableSet (S j) := hE.diff Metric.isOpen_ball.measurableSet
  have hmono : Monotone S := by
    intro i j hij x hx
    refine ⟨hx.1, ?_⟩
    intro hxj
    apply hx.2
    exact (Metric.ball_subset_ball (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)) hxj
  have hUnion : (⋃ j, S j) = E \ {p} := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.mp hx with ⟨j, hxj⟩
      refine ⟨hxj.1, ?_⟩
      intro hxp
      have heq : x = p := mem_singleton_iff.mp hxp
      apply hxj.2
      simp only [heq, Metric.mem_ball, dist_self]
      positivity
    · intro hx
      have hxp : x ≠ p := by simpa only [mem_singleton_iff] using hx.2
      obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).eventually_lt_const
          (dist_pos.mpr hxp)).exists
      apply mem_iUnion.mpr
      exact ⟨j, hx.1, fun hb => (not_lt_of_ge hj.le) (Metric.mem_ball.mp hb)⟩
  have hiUnion : IntegrableOn h (⋃ j, S j) μ := by
    rw [hUnion]
    exact hi.mono_set sdiff_subset
  have hlim := tendsto_setIntegral_of_monotone hSm hmono hiUnion
  have heq : (∫ x in ⋃ j, S j, h x ∂μ) = ∫ x in E, h x ∂μ := by
    rw [hUnion]
    exact setIntegral_congr_set (sdiff_null_ae_eq_self (measure_singleton p))
  rw [heq] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall (fun j => hbound _ (by positivity)))

end Poincare.CurvatureIntegral
