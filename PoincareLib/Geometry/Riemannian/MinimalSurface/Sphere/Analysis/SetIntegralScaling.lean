import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Admissibility under scalar changes of variables

Morgan-Tian Definition 18.17, printed p. 430. Copying an admissible disk
into a smaller concentric disk transports both integrability and its
almost-everywhere regularity. These are consequences of the exact Haar
measure transformation under an invertible scalar map.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Pointwise

namespace PoincareMT.M60

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [Measure.IsAddHaarMeasure μ]

/-- Integrability on a region is preserved by a nonzero scalar domain
change. Source: MT Definition 18.17, p. 430, collar change of variables. -/
theorem integrableOn_comp_smul_iff {F : Type*} [NormedAddCommGroup F]
    (f : E → F) (S : Set E) {c : ℝ} (hc : c ≠ 0) :
    IntegrableOn (fun x => f (c • x)) S μ ↔ IntegrableOn f (c • S) μ := by
  let e : E ≃ᵐ E := (Homeomorph.smul (Units.mk0 c hc)).toMeasurableEquiv
  have he : e ⁻¹' (c • S) = S := by
    ext x
    change c • x ∈ c • S ↔ x ∈ S
    rw [mem_smul_set_iff_inv_smul_mem₀ hc, inv_smul_smul₀ hc]
  have hi := integrableOn_map_equiv e (f := f) (s := c • S) (μ := μ)
  rw [he] at hi
  change IntegrableOn f (c • S) (μ.map (fun x => c • x)) ↔
    IntegrableOn (fun x => f (c • x)) S μ at hi
  rw [Measure.map_addHaar_smul μ hc] at hi
  have hpos : ENNReal.ofReal |(c ^ Module.finrank ℝ E)⁻¹| ≠ 0 := by
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le, abs_pos] using
      inv_ne_zero (pow_ne_zero (Module.finrank ℝ E) hc)
  simp only [IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure hpos ENNReal.ofReal_ne_top] at hi
  exact hi.symm

/-- A nonzero scalar domain change pulls back almost-everywhere
properties. Source: MT Definition 18.17, p. 430, collar admissibility. -/
theorem ae_comp_smul {p : E → Prop} (hp : ∀ᵐ x ∂μ, p x) {c : ℝ} (hc : c ≠ 0) :
    ∀ᵐ x ∂μ, p (c • x) := by
  have hp' : ∀ᵐ x ∂μ.map (fun x => c • x), p x := by
    rw [Measure.map_addHaar_smul μ hc]
    exact Measure.ae_smul_measure hp _
  exact ae_of_ae_map (measurable_const_smul c).aemeasurable hp'

end PoincareMT.M60
