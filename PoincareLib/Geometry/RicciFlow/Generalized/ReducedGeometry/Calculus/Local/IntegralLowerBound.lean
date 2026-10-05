import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# An integral lower bound from a lower bound on measure

The measure-theoretic step in Morgan-Tian equation (8.1), p. 170. Working
with the lower integral avoids assuming that the measurable region has finite
measure before integrability of the density has been used.
-/

set_option autoImplicit false

open scoped ENNReal

namespace MeasureTheory

/-- An integrable density bounded below by a nonnegative constant has integral
at least that constant times any real lower bound on the region's measure.
This is the abstract integral estimate used in Morgan-Tian equation (8.1), p. 170. -/
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
