import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Quadratic


noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.Analysis.Elliptic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem tendsto_integral_of_integral_abs_sub
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ k in atTop, Integrable (f k) μ) (hg : Integrable g μ)
    (hfg : Tendsto (fun k => ∫ x, |f k x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, f k x ∂μ) atTop (𝓝 (∫ x, g x ∂μ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _ hfg
  filter_upwards [hf] with k hk
  rw [← integral_sub hk hg]
  exact norm_integral_le_integral_norm _

theorem tendsto_integral_test_mul_of_integral_abs_sub
    {f : ℕ → X → ℝ} {g φ : X → ℝ} {C : ℝ}
    (hf : ∀ᶠ k in atTop, Integrable (f k) μ) (hg : Integrable g μ)
    (hφ : AEStronglyMeasurable φ μ) (hφb : ∀ᵐ x ∂μ, |φ x| ≤ C)
    (hfg : Tendsto (fun k => ∫ x, |f k x - g x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, φ x * f k x ∂μ) atTop (𝓝 (∫ x, φ x * g x ∂μ)) := by
  apply tendsto_integral_of_integral_abs_sub
    (hf.mono fun _ hk => hk.bdd_mul hφ hφb) (hg.bdd_mul hφ hφb)
  exact tendsto_integral_abs_coefficient_mul_sub
    (Eventually.of_forall fun _ => hφ) hφ
    (Eventually.of_forall fun _ => hφb) hφb
    (Eventually.of_forall fun _ => tendsto_const_nhds) hf hg hfg

end Poincare.Analysis.Elliptic
