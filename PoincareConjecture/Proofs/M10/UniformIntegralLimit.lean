import Mathlib.MeasureTheory.Integral.DominatedConvergence








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M10


theorem tendsto_integral_mul_of_uniform_error {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : ℕ → X → ℝ} {u v : X → ℝ} {ε : ℕ → ℝ}
    (hv : Integrable v μ) (huv : Integrable (fun x ↦ u x * v x) μ)
    (hfv : ∀ j, Integrable (fun x ↦ f j x * v x) μ)
    (hε : Tendsto ε atTop (𝓝 0))
    (herr : ∀ j, ∀ x ∈ Function.support v, |f j x - u x| ≤ ε j) :
    Tendsto (fun j ↦ ∫ x, f j x * v x ∂μ) atTop (𝓝 (∫ x, u x * v x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ |u x * v x| + |v x|)
    (Eventually.of_forall (fun j ↦ (hfv j).aestronglyMeasurable))
  · filter_upwards [hε (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with j hj
    exact Eventually.of_forall (fun x ↦ by
      rw [Real.norm_eq_abs]
      by_cases hx : v x = 0
      · simp only [hx, mul_zero, abs_zero, add_zero, le_refl]
      · have he := (herr j x hx).trans hj.le
        calc
          |f j x * v x| = |u x * v x + (f j x - u x) * v x| := by congr 1; ring
          _ ≤ |u x * v x| + |(f j x - u x) * v x| := abs_add_le _ _
          _ ≤ |u x * v x| + |v x| := by
            simp only [abs_mul]
            nlinarith [abs_nonneg (v x)])
  · exact huv.abs.add hv.abs
  · exact Eventually.of_forall (fun x ↦ by
      by_cases hx : v x = 0
      · simpa only [hx, mul_zero] using (tendsto_const_nhds (x := (0 : ℝ)))
      · have he : Tendsto (fun j ↦ f j x - u x) atTop (𝓝 0) :=
          squeeze_zero_norm (fun j ↦ by simpa only [Real.norm_eq_abs] using herr j x hx) hε
        have hf : Tendsto (fun j ↦ f j x) atTop (𝓝 (u x)) := by
          simpa only [sub_add_cancel, zero_add] using he.add (tendsto_const_nhds (x := u x))
        exact hf.mul tendsto_const_nhds)

end PoincareConjecture.M10
