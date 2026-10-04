import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Exhaustion of nonnegative parabolic energy

This file isolates the measure-theoretic passage used after the compactly
supported Karp--Li identity.  A family of cutoffs which converges to one on
every point cannot lose a nonnegative energy density: Fatou's lemma turns
uniform bounds for the cutoff energies into a finite global energy bound.
The geometric construction of the cutoffs and the compact identity live in
the Riemannian heat modules.
-/

set_option autoImplicit false

open MeasureTheory Filter
open scoped Topology

namespace Poincare.Parabolic

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Fatou passage for a nonnegative energy density and an exhausting cutoff.

The hypotheses are stated for `ofReal` so that the result applies to an
arbitrary measurable space and does not require a locally compact model. -/
theorem hasFiniteIntegral_of_cutoff_lintegral_bound
    {q : α → ℝ} (hq : 0 ≤ᵐ[μ] q)
    (hqmeas : AEMeasurable q μ)
    (χ : ℕ → α → ℝ)
    (hχmeas : ∀ j, AEMeasurable (χ j) μ)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun j ↦ χ j x) atTop (𝓝 1))
    {C : ℝ}
    (hbound : ∀ j, (∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) ≤ ENNReal.ofReal C) :
    HasFiniteIntegral q μ ∧
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤ ENNReal.ofReal C := by
  have hq_nonneg : ∀ᵐ x ∂μ, ENNReal.ofReal (q x) =
      liminf (fun j ↦ ENNReal.ofReal (χ j x * q x)) atTop := by
    filter_upwards [hχlim] with x hlim
    have hprod : Tendsto (fun j ↦ χ j x * q x) atTop (𝓝 (1 * q x)) := by
      exact (hlim.mul tendsto_const_nhds)
    have hprod' : Tendsto (fun j ↦ χ j x * q x) atTop (𝓝 (q x)) := by
      simpa using hprod
    have hof : Tendsto (fun j ↦ ENNReal.ofReal (χ j x * q x)) atTop
        (𝓝 (ENNReal.ofReal (q x))) :=
      (ENNReal.continuous_ofReal.tendsto _).comp hprod'
    exact hof.liminf_eq.symm
  have hfatou : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤
      liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) atTop := by
    calc
      (∫⁻ x, ENNReal.ofReal (q x) ∂μ) =
          ∫⁻ x, liminf (fun j ↦ ENNReal.ofReal (χ j x * q x)) atTop ∂μ :=
        lintegral_congr_ae hq_nonneg
      _ ≤ liminf (fun j ↦ ∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) atTop := by
        apply lintegral_liminf_le'
        intro j
        exact ((hχmeas j).mul hqmeas).ennreal_ofReal
  have hlimbound : liminf (fun j ↦
      ∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) atTop ≤ ENNReal.ofReal C := by
    exact liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  have hglobal : (∫⁻ x, ENNReal.ofReal (q x) ∂μ) ≤ ENNReal.ofReal C :=
    hfatou.trans hlimbound
  refine ⟨?_, hglobal⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hnorm : (∫⁻ x, ‖q x‖ₑ ∂μ) = ∫⁻ x, ENNReal.ofReal (q x) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [hq] with x hx
    exact Real.enorm_of_nonneg hx
  rw [hnorm]
  exact (hglobal.trans_lt ENNReal.ofReal_lt_top)

/-- Real-valued form of the cutoff exhaustion lemma.

Each cutoff energy is assumed integrable and nonnegative; its ordinary
integral bound is converted to the lower Lebesgue integral before applying the
previous theorem. -/
theorem integrable_of_cutoff_integral_bound
    {q : α → ℝ} (hq : 0 ≤ᵐ[μ] q)
    (hqmeas : AEMeasurable q μ)
    (χ : ℕ → α → ℝ)
    (hχmeas : ∀ j, AEMeasurable (χ j) μ)
    (hχnonneg : ∀ j, 0 ≤ᵐ[μ] χ j)
    (hχlim : ∀ᵐ x ∂μ, Tendsto (fun j ↦ χ j x) atTop (𝓝 1))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ j, Integrable (fun x ↦ χ j x * q x) μ ∧
      (∫ x, χ j x * q x ∂μ) ≤ C) :
    Integrable q μ ∧ (∫ x, q x ∂μ) ≤ C := by
  have hbound' : ∀ j, (∫⁻ x, ENNReal.ofReal (χ j x * q x) ∂μ) ≤ ENNReal.ofReal C := by
    intro j
    have hnonneg : 0 ≤ᵐ[μ] fun x ↦ χ j x * q x := by
      filter_upwards [hχnonneg j, hq] with x hχ hq'
      exact mul_nonneg hχ hq'
    have hEq := ofReal_integral_eq_lintegral_ofReal (hbound j).1 hnonneg
    rw [← hEq]
    exact ENNReal.ofReal_le_ofReal (hbound j).2
  obtain ⟨hfi, hlin⟩ := hasFiniteIntegral_of_cutoff_lintegral_bound hq hqmeas χ hχmeas
    hχlim hbound'
  have hqint : Integrable q μ := ⟨hqmeas.aestronglyMeasurable, hfi⟩
  refine ⟨hqint, ?_⟩
  apply (ENNReal.ofReal_le_ofReal_iff hC).mp
  rw [ofReal_integral_eq_lintegral_ofReal hqint hq]
  exact hlin

end Poincare.Parabolic
