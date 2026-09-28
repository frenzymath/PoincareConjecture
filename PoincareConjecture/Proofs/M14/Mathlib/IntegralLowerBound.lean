import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open scoped ENNReal

namespace MeasureTheory

theorem mul_le_setIntegral_of_measure_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S : Set α} {f : α → ℝ} {c V : ℝ}
    (hc : 0 ≤ c) (hf : IntegrableOn f S μ) (hμ : ENNReal.ofReal V ≤ μ S)
    (hbound : ∀ᵐ q ∂μ.restrict S, c ≤ f q) : c * V ≤ ∫ q in S, f q ∂μ := by
  have hf0 : 0 ≤ᵐ[μ.restrict S] f := hbound.mono (fun _ hq => hc.trans hq)
  apply (ENNReal.ofReal_le_ofReal_iff (integral_nonneg_of_ae hf0)).mp
  calc
    ENNReal.ofReal (c * V) = ENNReal.ofReal c * ENNReal.ofReal V :=
      ENNReal.ofReal_mul hc
    _ ≤ ENNReal.ofReal c * μ S := mul_le_mul_right hμ _
    _ = ∫⁻ _q in S, ENNReal.ofReal c ∂μ := by simp
    _ ≤ ∫⁻ q in S, ENNReal.ofReal (f q) ∂μ :=
      lintegral_mono_ae (hbound.mono (fun _ hq => ENNReal.ofReal_le_ofReal hq))
    _ = ENNReal.ofReal (∫ q in S, f q ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hf hf0).symm

end MeasureTheory
