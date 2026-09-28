import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false

open Set MeasureTheory MeasureTheory.Measure

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (μ : Measure E) [IsAddHaarMeasure μ]

theorem criticalValues_null (f : E → E) (s : Set E)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    μ (f '' {x ∈ s | (fderiv ℝ f x).det = 0}) = 0 := by
  exact addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
    (fun x hx => (hf x hx.1).hasFDerivAt.hasFDerivWithinAt)
    (fun _ hx => hx.2)

theorem dense_opposite_regularValues [Measure.IsNegInvariant μ]
    (f : E → E) (s : Set E) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) :
    Dense {v : E | (∀ x ∈ s, f x = v → (fderiv ℝ f x).det ≠ 0) ∧
      (∀ x ∈ s, f x = -v → (fderiv ℝ f x).det ≠ 0)} := by
  let C : Set E := f '' {x ∈ s | (fderiv ℝ f x).det = 0}
  have hC : μ C = 0 := criticalValues_null μ f s hf
  have hneg : μ (Neg.neg ⁻¹' C) = 0 := by
    rw [Measure.measure_preimage_neg, hC]
  have hgood : ∀ᵐ v ∂μ, v ∉ C ∧ -v ∉ C := by
    have hfirst : ∀ᵐ v ∂μ, v ∉ C := measure_eq_zero_iff_ae_notMem.mp hC
    have hsecond : ∀ᵐ v ∂μ, -v ∉ C := by
      exact measure_eq_zero_iff_ae_notMem.mp hneg
    exact hfirst.and hsecond
  apply Measure.dense_of_ae (μ := μ)
  filter_upwards [hgood] with v hv
  constructor
  · intro x hx hxv hdet
    exact hv.1 ⟨x, ⟨hx, hdet⟩, hxv⟩
  · intro x hx hxv hdet
    exact hv.2 ⟨x, ⟨hx, hdet⟩, hxv⟩

end PoincareConjecture.M25.Topology3D
