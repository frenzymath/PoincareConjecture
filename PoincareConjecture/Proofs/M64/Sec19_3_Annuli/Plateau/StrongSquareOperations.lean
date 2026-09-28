import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {mu : Measure X}

theorem m64StrongSquare_smul
    (f : ℕ → X → E) (hf : ∀ j, MemLp (f j) 2 mu)
    (a : X → ℝ) (ha : AEStronglyMeasurable a mu)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ x ∂mu, ‖a x‖ ≤ C)
    (hlim : Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖a x • f j x‖ ^ 2 ∂mu) atTop (𝓝 0) := by
  have hat : MemLp a ∞ mu := memLp_top_of_bound ha C hb
  have hi (j : ℕ) : Integrable (fun x => ‖f j x‖ ^ 2) mu :=
    (memLp_two_iff_integrable_sq_norm (hf j).aestronglyMeasurable).mp (hf j)
  have hai (j : ℕ) : Integrable (fun x => ‖a x • f j x‖ ^ 2) mu := by
    have hh : MemLp (fun x => a x • f j x) 2 mu := MemLp.smul (hf j) hat
    exact (memLp_two_iff_integrable_sq_norm hh.aestronglyMeasurable).mp hh
  have bound (j : ℕ) : (∫ x, ‖a x • f j x‖ ^ 2 ∂mu) ≤
      C ^ 2 * ∫ x, ‖f j x‖ ^ 2 ∂mu := by
    rw [← integral_const_mul]
    apply integral_mono_ae (hai j) ((hi j).const_mul _)
    filter_upwards [hb] with x hx
    rw [norm_smul, mul_pow]
    exact mul_le_mul_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) hC).mpr hx) (sq_nonneg _)
  have hl := hlim.const_mul (C ^ 2)
  simp only [mul_zero] at hl
  exact squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg _)) bound hl

omit [NormedSpace ℝ E] in

theorem m64StrongSquare_add
    (f g : ℕ → X → E) (hf : ∀ j, MemLp (f j) 2 mu) (hg : ∀ j, MemLp (g j) 2 mu)
    (hf0 : Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂mu) atTop (𝓝 0))
    (hg0 : Tendsto (fun j => ∫ x, ‖g j x‖ ^ 2 ∂mu) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖f j x + g j x‖ ^ 2 ∂mu) atTop (𝓝 0) := by
  have hfi (j : ℕ) := (memLp_two_iff_integrable_sq_norm
    (hf j).aestronglyMeasurable).mp (hf j)
  have hgi (j : ℕ) := (memLp_two_iff_integrable_sq_norm
    (hg j).aestronglyMeasurable).mp (hg j)
  have hfg (j : ℕ) := (memLp_two_iff_integrable_sq_norm
    ((hf j).add (hg j)).aestronglyMeasurable).mp ((hf j).add (hg j))
  have bound (j : ℕ) : (∫ x, ‖f j x + g j x‖ ^ 2 ∂mu) ≤
      2 * ((∫ x, ‖f j x‖ ^ 2 ∂mu) + ∫ x, ‖g j x‖ ^ 2 ∂mu) := by
    rw [← integral_add (hfi j) (hgi j), ← integral_const_mul]
    apply integral_mono (hfg j) ((hfi j).add (hgi j) |>.const_mul 2)
    intro x
    have hsq := (sq_le_sq₀ (norm_nonneg (f j x + g j x))
      (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (norm_add_le (f j x) (g j x))
    simp only [Pi.add_apply] at *
    nlinarith [sq_nonneg (‖f j x‖ - ‖g j x‖)]
  have hl := (hf0.add hg0).const_mul 2
  simp only [add_zero, mul_zero] at hl
  exact squeeze_zero (fun j => integral_nonneg (fun x => sq_nonneg _)) bound hl

end PoincareConjecture
