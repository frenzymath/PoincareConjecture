import PoincareLib.Geometry.CurveShortening.Comparison.Analysis.Endpoint.Cutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Endpoint cutoff limits in L1 pairings

This is the dominated convergence step in M64's second-stress-cutoff
derivation for Lemaire 1982, Lemma 5.1, p. 99. The field is only L1;
no boundary trace or derivative of that field is used.

Morgan--Tian context: Lemma 19.15, printed pp. 447-449. This project analytic helper
supports the actual annular minimizer and boundary regularity construction.
-/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT

/-- Endpoint cutoff values and first derivatives converge in every L1 pairing. Source: M64's
second-stress-cutoff derivation. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-second-stress-cutoff.md, endpoint cutoff
construction. -/
theorem m64EndpointCutoff_integral_tendsto
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {mu : Measure X} {q : X → ℝ} {a b : ℝ}
    (hq : Measurable q) (hI : ∀ᵐ x ∂mu, q x ∈ Ioo a b)
    {F : X → E} (hF : Integrable F mu) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ∞ f) (ha : f a = 0) (hb : f b = 0) :
    Tendsto (fun j => ∫ x, m64EndpointCutoff a b f j (q x) • F x ∂mu) atTop
      (𝓝 (∫ x, f (q x) • F x ∂mu)) ∧
    Tendsto (fun j => ∫ x, deriv (m64EndpointCutoff a b f j) (q x) • F x ∂mu) atTop
      (𝓝 (∫ x, deriv f (q x) • F x ∂mu)) := by
  obtain ⟨C, -, hC⟩ := m64EndpointCutoff_uniform_bound hf ha hb
  constructor
  · apply tendsto_integral_of_dominated_convergence (fun x => C * ‖F x‖)
    · intro j
      exact (((m64EndpointCutoff_contDiff hf j).continuous.measurable.comp hq
        ).aestronglyMeasurable).smul hF.aestronglyMeasurable
    · exact hF.norm.const_mul C
    · intro j
      filter_upwards [hI] with x hx
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC j (q x) (Ioo_subset_Icc_self hx)).1 (norm_nonneg _)
    · filter_upwards [hI] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [m64EndpointCutoff_eventually hf hx] with j hj
      rw [hj.1]
  · apply tendsto_integral_of_dominated_convergence (fun x => C * ‖F x‖)
    · intro j
      have hc := (m64EndpointCutoff_contDiff (a := a) (b := b) hf j).continuous_deriv (by simp)
      exact (hc.measurable.comp hq).aestronglyMeasurable.smul hF.aestronglyMeasurable
    · exact hF.norm.const_mul C
    · intro j
      filter_upwards [hI] with x hx
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hC j (q x) (Ioo_subset_Icc_self hx)).2 (norm_nonneg _)
    · filter_upwards [hI] with x hx
      apply tendsto_const_nhds.congr'
      filter_upwards [m64EndpointCutoff_eventually hf hx] with j hj
      rw [hj.2]

end PoincareMT
