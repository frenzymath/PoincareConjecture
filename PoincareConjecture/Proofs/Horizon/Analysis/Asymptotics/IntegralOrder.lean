import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Poincare.Analysis

theorem exists_subseq_tendsto_ae_of_integral_abs_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : ℕ → X → ℝ} {g : X → ℝ}
    (hf : ∀ᶠ k in atTop, Integrable (f k) μ) (hg : Integrable g μ)
    (hfg : Tendsto (fun k => ∫ x, |f k x - g x| ∂μ) atTop (𝓝 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ᵐ x ∂μ, Tendsto (fun k => f (σ k) x) atTop (𝓝 (g x)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hf
  have hi (k : ℕ) : Integrable (f (k + N)) μ := hN _ (Nat.le_add_left N k)
  have hnorm : Tendsto (fun k => eLpNorm (f (k + N) - g) 1 μ) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (hfg.comp (tendsto_add_atTop_nat N))
    simp only [ENNReal.ofReal_zero] at h
    convert h using 1
    ext k
    rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm ((hi k).sub hg)]
    simp only [Pi.sub_apply, Real.norm_eq_abs, Function.comp_def]
  obtain ⟨σ, hσ, hpoint⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (fun k => (hi k).aestronglyMeasurable) hg.aestronglyMeasurable hnorm).exists_seq_tendsto_ae
  exact ⟨fun k => σ k + N, fun _ _ h => Nat.add_lt_add_right (hσ h) N, hpoint⟩

theorem ae_le_of_tendsto_integral_abs_sub
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f b : ℕ → X → ℝ} {g c : X → ℝ}
    (hf : ∀ᶠ k in atTop, Integrable (f k) μ) (hg : Integrable g μ)
    (hfg : Tendsto (fun k => ∫ x, |f k x - g x| ∂μ) atTop (𝓝 0))
    (hb : ∀ᶠ k in atTop, ∀ᵐ x ∂μ, f k x ≤ b k x)
    (hbc : ∀ᵐ x ∂μ, Tendsto (fun k => b k x) atTop (𝓝 (c x))) :
    ∀ᵐ x ∂μ, g x ≤ c x := by
  obtain ⟨σ, hσ, hpoint⟩ := exists_subseq_tendsto_ae_of_integral_abs_sub hf hg hfg
  obtain ⟨N, hN⟩ := eventually_atTop.1 hb
  have hall : ∀ᵐ x ∂μ, ∀ k : ℕ, N ≤ k → f k x ≤ b k x := by
    apply ae_all_iff.mpr
    intro k
    by_cases hk : N ≤ k
    · exact (hN k hk).mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (hk h).elim
  filter_upwards [hpoint, hall, hbc] with x hx hxb hxc
  exact le_of_tendsto_of_tendsto hx (hxc.comp hσ.tendsto_atTop)
    ((hσ.tendsto_atTop.eventually (eventually_ge_atTop N)).mono fun k hk => hxb (σ k) hk)

end Poincare.Analysis
