import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.Interior.Kernel.CenteredEstimate








set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal

namespace Poincare.Parabolic.Interior.Kernel

variable {V F : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
  [Nontrivial V] [NormedSpace ℝ F] in

theorem centered_bound_of_vanishes_on_ball
    {α Q r : ℝ} (hα : 0 ≤ α) (hQ : 0 ≤ Q) (hr : 0 < r)
    {f : V → F} (hb : ∀ y, ‖f y‖ ≤ Q)
    (hz : ∀ y, ‖y‖ < r → f y = 0) (y : V) :
    ‖f y‖ ≤ (Q / r ^ α) * ‖y‖ ^ α := by
  by_cases hy : ‖y‖ < r
  · rw [hz y hy, norm_zero]
    positivity
  · have hp : 0 < r ^ α := Real.rpow_pos_of_pos hr _
    have hm : r ^ α ≤ ‖y‖ ^ α := Real.rpow_le_rpow hr.le (le_of_not_gt hy) hα
    calc
      ‖f y‖ ≤ Q := hb y
      _ = (Q / r ^ α) * r ^ α := (div_mul_cancel₀ Q hp.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hm (div_nonneg hQ hp.le)


theorem norm_integral_heatD2_smul_le_of_bound
    {Q t : ℝ} (hQ : 0 ≤ Q) (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ Q) (v w : V) :
    ‖∫ y, heatD2 t v w y • f y‖ ≤ ‖v‖ * ‖w‖ * Q * t⁻¹ * heatC2 V := by
  calc
    _ ≤ ∫ y, ‖heatD2 t v w y‖ * Q := by
      apply norm_integral_le_of_norm_le ((heatD2_int ht v w).norm.mul_const Q)
      exact Filter.Eventually.of_forall fun y => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (hf y) (norm_nonneg _)
    _ = (∫ y, ‖heatD2 t v w y‖) * Q := integral_mul_const Q _
    _ ≤ (‖v‖ * ‖w‖ * t⁻¹ * heatC2 V) * Q :=
      mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) hQ
    _ = _ := by ring


theorem norm_hessian_potential_le_of_time_gap
    {Q δ t : ℝ} (hQ : 0 ≤ Q) (hδ : 0 < δ) (ht : 0 < t)
    {f : ℝ → V → F}
    (hf : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y, ‖f s y‖ ≤ Q)
    (hz : ∀ s ∈ Ioo (0 : ℝ) t, t - δ < s → ∀ y, f s y = 0)
    (v w : V) :
    ‖∫ s in 0..t, ∫ y, heatD2 (t - s) v w y • f s y‖ ≤
      (‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V) * t := by
  have hC : 0 ≤ ‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V := by
    exact mul_nonneg (by positivity) (heatC2_nonneg (V := V))
  have hb : ∀ s ∈ Ioo (0 : ℝ) t,
      ‖∫ y, heatD2 (t - s) v w y • f s y‖ ≤
        ‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V := by
    intro s hs
    by_cases hg : t - δ < s
    · simpa only [hz s hs hg, smul_zero, integral_zero, norm_zero] using hC
    · refine (norm_integral_heatD2_smul_le_of_bound hQ (sub_pos.mpr hs.2)
        (hf s hs) v w).trans ?_
      have hgap : δ ≤ t - s := by linarith
      gcongr
      exact heatC2_nonneg (V := V)
  calc
    _ ≤ ∫ _s in 0..t, ‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.le ?_ intervalIntegrable_const
      have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with s hst hs
      exact hb s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    _ = _ := by rw [intervalIntegral.integral_const]; simp [smul_eq_mul, mul_comm]



theorem norm_integral_heatD2_smul_le_of_centered_add_bound
    {α : ℝ≥0} (hα : α ≤ 1) {K Q t : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (ht : 0 < t) {f : V → F}
    (hf : ∀ y, ‖f y‖ ≤ K * ‖y‖ ^ (α : ℝ) + Q) (v w : V) :
    ‖∫ y, heatD2 t v w y • f y‖ ≤
      ‖v‖ * ‖w‖ * K * holderHeatScale α t * heatC2Holder (V := V) α +
        ‖v‖ * ‖w‖ * Q * t⁻¹ * heatC2 V := by
  have h₁ := (heatD2Holder_int (V := V) hα ht).const_mul (‖v‖ * ‖w‖ * K)
  have h₂ := (heatD2_int ht v w).norm.mul_const Q
  calc
    _ ≤ ∫ y, (‖v‖ * ‖w‖ * K) * heatD2Holder α t y + ‖heatD2 t v w y‖ * Q := by
      apply norm_integral_le_of_norm_le (h₁.add h₂)
      apply Filter.Eventually.of_forall
      intro y
      calc
        _ = ‖heatD2 t v w y‖ * ‖f y‖ := norm_smul _ _
        _ ≤ ‖heatD2 t v w y‖ * (K * ‖y‖ ^ (α : ℝ) + Q) := by gcongr; exact hf y
        _ = K * (‖heatD2 t v w y‖ * ‖y‖ ^ (α : ℝ)) + ‖heatD2 t v w y‖ * Q := by ring
        _ ≤ K * (‖v‖ * ‖w‖ * heatD2Holder α t y) + ‖heatD2 t v w y‖ * Q := by
          exact add_le_add (mul_le_mul_of_nonneg_left
            (heatD2_holder_bound α ht v w y) hK) le_rfl
        _ = _ := by simp only [Pi.add_apply]; ring
    _ = (‖v‖ * ‖w‖ * K) * (∫ y : V, heatD2Holder α t y) +
        (∫ y, ‖heatD2 t v w y‖) * Q := by
      rw [integral_add h₁ h₂, integral_const_mul, integral_mul_const]
    _ ≤ ‖v‖ * ‖w‖ * K * holderHeatScale α t * heatC2Holder (V := V) α +
        ‖v‖ * ‖w‖ * Q * t⁻¹ * heatC2 V := by
      rw [integral_heatD2Holder α ht, holderHeatScale_eq α ht]
      have := mul_le_mul_of_nonneg_right (integral_norm_D2 ht v w) hQ
      nlinarith



theorem norm_hessian_potential_le_of_centered_add_time_gap
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) {K Q δ t : ℝ}
    (hK : 0 ≤ K) (hQ : 0 ≤ Q) (hδ : 0 < δ) (ht : 0 < t)
    {f : ℝ → V → F}
    (hf : ∀ s ∈ Ioo (0 : ℝ) t, ∀ y, ‖f s y‖ ≤ K * ‖y‖ ^ (α : ℝ) + Q)
    (hlate : ∀ s ∈ Ioo (0 : ℝ) t, t - δ < s → ∀ y,
      ‖f s y‖ ≤ K * ‖y‖ ^ (α : ℝ)) (v w : V) :
    ‖∫ s in 0..t, ∫ y, heatD2 (t - s) v w y • f s y‖ ≤
      (‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α) *
        ((2 / (α : ℝ)) * t ^ ((α : ℝ) / 2)) +
      (‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V) * t := by
  let A := ‖v‖ * ‖w‖ * K * heatC2Holder (V := V) α
  let D := ‖v‖ * ‖w‖ * Q * δ⁻¹ * heatC2 V
  have hD : 0 ≤ D := mul_nonneg (by positivity) (heatC2_nonneg (V := V))
  have hb : ∀ s ∈ Ioo (0 : ℝ) t,
      ‖∫ y, heatD2 (t - s) v w y • f s y‖ ≤ A * holderHeatScale α (t - s) + D := by
    intro s hs
    by_cases hg : t - δ < s
    · have h := norm_integral_heatD2_smul_le_of_centered_bound hα1
        (sub_pos.mpr hs.2) (hlate s hs hg) v w
      dsimp [A]
      nlinarith
    · have h := norm_integral_heatD2_smul_le_of_centered_add_bound hα1 hK hQ
        (sub_pos.mpr hs.2) (hf s hs) v w
      have hgap : δ ≤ t - s := by linarith
      have hle : ‖v‖ * ‖w‖ * Q * (t - s)⁻¹ * heatC2 V ≤ D := by
        dsimp [D]
        gcongr
        exact heatC2_nonneg (V := V)
      dsimp [A]
      nlinarith
  have hmajor := (holderHeatScale_intble hα0 (t := t)).const_mul A
  calc
    _ ≤ ∫ s in 0..t, A * holderHeatScale α (t - s) + D := by
      refine intervalIntegral.norm_integral_le_of_norm_le ht.le ?_
        (hmajor.add intervalIntegrable_const)
      have hne : ∀ᵐ s ∂(volume : Measure ℝ), s ≠ t := by
        simp [ae_iff, measure_singleton]
      filter_upwards [hne] with s hst hs
      exact hb s ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    _ = _ := by
      rw [intervalIntegral.integral_add hmajor intervalIntegrable_const,
        intervalIntegral.integral_const_mul, timeHolderHeatScale_int hα0,
        intervalIntegral.integral_const]
      simp only [sub_zero, smul_eq_mul, A, D]
      ring

end Poincare.Parabolic.Interior.Kernel
