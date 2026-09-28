import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.HolderMoment

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [CompleteSpace F] in

theorem norm_heatD2_smul_le_of_centered_bound
    {α : ℝ≥0} {K t : ℝ} (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ K * ‖y‖ ^ (α : ℝ)) (v w y : V) :
    ‖heatD2 t v w y • f y‖ ≤ ‖v‖ * ‖w‖ * K * heatD2Holder α t y := by
  calc
    ‖heatD2 t v w y • f y‖ = ‖heatD2 t v w y‖ * ‖f y‖ := norm_smul _ _
    _ ≤ ‖heatD2 t v w y‖ * (K * ‖y‖ ^ (α : ℝ)) :=
      mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _)
    _ = K * (‖heatD2 t v w y‖ * ‖y‖ ^ (α : ℝ)) := by ring
    _ ≤ K * (‖v‖ * ‖w‖ * heatD2Holder α t y) := by
      by_cases hK : 0 ≤ K
      · exact mul_le_mul_of_nonneg_left (heatD2_holder_bound α ht v w y) hK
      · have hnonpos : K * ‖y‖ ^ (α : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hK)
            (Real.rpow_nonneg (norm_nonneg _) _)
        have hy : ‖y‖ ^ (α : ℝ) = 0 := by
          have := (norm_nonneg (f y)).trans (hf y)
          nlinarith
        rw [heatD2Holder_eq α ht, hy]
        simp
    _ = ‖v‖ * ‖w‖ * K * heatD2Holder α t y := by ring

omit [CompleteSpace F] in

theorem integrable_heatD2_smul_of_centered_bound
    {α : ℝ≥0} (hα : α ≤ 1) {K t : ℝ} (ht : 0 < t) {f : V → F}
    (hm : AEStronglyMeasurable f)
    (hf : ∀ y, ‖f y‖ ≤ K * ‖y‖ ^ (α : ℝ)) (v w : V) :
    Integrable (fun y => heatD2 t v w y • f y) := by
  refine ((heatD2Holder_int hα ht).const_mul (‖v‖ * ‖w‖ * K)).mono' ?_ ?_
  · exact (heatD2_int ht v w).aestronglyMeasurable.smul hm
  · exact Filter.Eventually.of_forall (norm_heatD2_smul_le_of_centered_bound ht hf v w)

omit [CompleteSpace F] in

theorem norm_integral_heatD2_smul_le_of_centered_bound
    {α : ℝ≥0} (hα : α ≤ 1) {K t : ℝ} (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ K * ‖y‖ ^ (α : ℝ)) (v w : V) :
    ‖∫ y, heatD2 t v w y • f y‖ ≤
      ‖v‖ * ‖w‖ * K * holderHeatScale α t * heatC2Holder (V := V) α := by
  calc
    ‖∫ y, heatD2 t v w y • f y‖ ≤
        ∫ y, (‖v‖ * ‖w‖ * K) * heatD2Holder α t y :=
      norm_integral_le_of_norm_le ((heatD2Holder_int hα ht).const_mul _)
        (Filter.Eventually.of_forall (norm_heatD2_smul_le_of_centered_bound ht hf v w))
    _ = ‖v‖ * ‖w‖ * K * holderHeatScale α t * heatC2Holder (V := V) α := by
      rw [integral_const_mul, integral_heatD2Holder α ht, holderHeatScale_eq α ht]
      ring

omit [CompleteSpace F] in

theorem norm_hessian_potential_le_of_centered_bound
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) {K t : ℝ}
    (ht : 0 < t) {f : ℝ → V → F}
    (hf : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y, ‖f s y‖ ≤ K * ‖y‖ ^ (α : ℝ))
    (v w : V) :
    ‖∫ s in 0..t, ∫ y, heatD2 (t - s) v w y • f s y‖ ≤
      (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) := by
  have hmajor := (holderHeatScale_intble hα0 (t := t)).const_mul
    (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α)
  have hbound : ∀ s ∈ Ioo (0 : ℝ) t,
      ‖∫ y, heatD2 (t - s) v w y • f s y‖ ≤
        (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) * holderHeatScale α (t - s) := by
    intro s hs
    exact (norm_integral_heatD2_smul_le_of_centered_bound hα1
      (sub_pos.mpr hs.2) (hf s hs) v w).trans_eq (by ring)
  calc
    ‖∫ s in 0..t, ∫ y, heatD2 (t - s) v w y • f s y‖ ≤
        ∫ s in 0..t, (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) *
          holderHeatScale α (t - s) := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.le ?_ hmajor
      have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with s hst hs
      exact hbound s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, timeHolderHeatScale_int hα0]

end Poincare.Parabolic.Interior.Kernel
