import Mathlib.MeasureTheory.Measure.WithDensity

/-!
Adapted from Mapher `PoincareMT/Proofs/M10/DensityComparison.lean` at
revision `f927d9e1f0810042766d3b5f64d3f4da02ee93cc`.

# Measure bounds from local multiplicative density bounds

Pointwise comparison with a constant density gives both measure
inequalities without cancellation, also for sets of infinite measure.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PoincareMT.SurgeryVolume.Measure

variable {X : Type*} [MeasurableSpace X]

/-- Local real density bounds give two ENNReal measure bounds with the same factor. -/
theorem withDensity_comparison_of_local_bounds (μ : Measure X)
    {J : X → ℝ} {A : Set X} (hA : MeasurableSet A)
    {c : ℝ} {r : ℝ≥0} (hr : (0 : ℝ) < r)
    (hlo : ∀ x ∈ A, c / r ≤ J x) (hhi : ∀ x ∈ A, J x ≤ r * c) :
    ENNReal.ofReal c * μ A ≤ (r : ℝ≥0∞) * (μ.withDensity (fun x ↦ ENNReal.ofReal (J x))) A ∧
      (μ.withDensity (fun x ↦ ENNReal.ofReal (J x))) A ≤
        (r : ℝ≥0∞) * ENNReal.ofReal c * μ A := by
  constructor
  · calc
      _ = ∫⁻ x in A, ENNReal.ofReal c ∂μ := by simp
      _ ≤ ∫⁻ x in A, (r : ℝ≥0∞) * ENNReal.ofReal (J x) ∂μ := by
        apply setLIntegral_mono' hA
        intro x hx
        have hreal : c ≤ (r : ℝ) * J x := by
          simpa only [mul_comm] using (div_le_iff₀ hr).mp (hlo x hx)
        simpa only [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top, withDensity_apply _ hA]
  · rw [withDensity_apply _ hA]
    calc
      _ ≤ ∫⁻ x in A, (r : ℝ≥0∞) * ENNReal.ofReal c ∂μ := by
        apply setLIntegral_mono' hA
        intro x hx
        simpa only [ENNReal.ofReal_mul hr.le, ENNReal.ofReal_coe_nnreal] using
          ENNReal.ofReal_le_ofReal (hhi x hx)
      _ = _ := by simp

end PoincareMT.SurgeryVolume.Measure
