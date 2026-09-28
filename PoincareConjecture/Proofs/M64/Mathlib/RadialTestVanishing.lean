import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace PoincareConjecture

theorem radialCoefficient_ae_eq_zero_of_test_pairings
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {a b : ℝ} {mu : Measure ℝ} {f : ℝ → F}
    (hf : LocallyIntegrableOn f (Ioo (a ^ 2) (b ^ 2)) mu)
    (h : ∀ psi : ℝ → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ Ioo (a ^ 2) (b ^ 2) → ∫ t, psi t • f t ∂mu = 0) :
    ∀ᵐ t ∂mu.restrict (Ioo (a ^ 2) (b ^ 2)), f t = 0 := by
  exact (ae_restrict_iff' measurableSet_Ioo).mpr
    (isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero hf h)

theorem ae_and_exists_mem_of_measure_ne_zero
    {X : Type*} [MeasurableSpace X] {mu : Measure X} {s : Set X}
    (hs : mu s ≠ 0) {P Q : X → Prop}
    (hP : ∀ᵐ x ∂mu.restrict s, P x) (hQ : ∀ᵐ x ∂mu.restrict s, Q x) :
    (∀ᵐ x ∂mu.restrict s, P x ∧ Q x) ∧ ∃ x ∈ s, P x ∧ Q x := by
  exact ⟨hP.and hQ, Measure.exists_mem_of_measure_ne_zero_of_ae hs (hP.and hQ)⟩

theorem exists_common_good_radius_of_ae
    {a b : ℝ} (hab : a < b) {P Q : ℝ → Prop}
    (hP : ∀ᵐ r ∂volume.restrict (Ioo a b), P r)
    (hQ : ∀ᵐ r ∂volume.restrict (Ioo a b), Q r) :
    (∀ᵐ r ∂volume.restrict (Ioo a b), P r ∧ Q r) ∧
      ∃ r ∈ Ioo a b, P r ∧ Q r := by
  apply ae_and_exists_mem_of_measure_ne_zero (hP := hP) (hQ := hQ)
  rw [Real.volume_Ioo]
  exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab)).ne'

end PoincareConjecture
