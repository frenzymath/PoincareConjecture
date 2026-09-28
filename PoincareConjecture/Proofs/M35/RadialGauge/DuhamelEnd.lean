import PoincareConjecture.Proofs.M35.RadialGauge.DerivativeKernelEnd

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)

theorem heatDuhamel_weighted_vanishes_uniformly
    {f : ℝ → V → F} {C T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ s ∈ Icc 0 T, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hend : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      R ≤ ‖x‖ → (1 + ‖x‖) * ‖f s x‖ < e) :
    ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖heatDuhamel f t x‖ < e := by
  intro e he
  let d := e / (T + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨R, hR⟩ := heatAverage_weighted_vanishes_uniformly
    (f := fun s : Icc 0 T => f s.1) (T := T)
    (fun s => hf s.1 s.2) (fun s => hbound s.1 s.2)
    (fun a ha => by
      obtain ⟨R, hR⟩ := hend a ha
      exact ⟨R, fun s => hR s.1 s.2⟩) d hd
  refine ⟨R, fun t ht x hx => ?_⟩
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun s => (1 + ‖x‖) • heatAverage (t - s) (f s) x)
    (C := d) (by
      intro s hs
      rw [uIoc_of_le ht.1] at hs
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      exact (hR ⟨s, hs.1.le, hs.2.trans ht.2⟩ (t - s)
        ⟨sub_nonneg.mpr hs.2, (sub_le_self t hs.1.le).trans ht.2⟩ x hx).le)
  rw [intervalIntegral.integral_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hw, sub_zero, abs_of_nonneg ht.1] at h
  have hdeq : d * (T + 1) = e := div_mul_cancel₀ _ (by positivity)
  change (1 + ‖x‖) * ‖heatDuhamel f t x‖ ≤ _ at h
  have hdt := mul_le_mul_of_nonneg_left ht.2 hd.le
  nlinarith

theorem heatDuhamelGradient_weighted_vanishes_uniformly
    {f : ℝ → V → F} {C T : ℝ}
    (hf : ∀ s ∈ Icc 0 T, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 T, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C)
    (hend : ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ s ∈ Icc 0 T, ∀ x,
      R ≤ ‖x‖ → (1 + ‖x‖) * ‖f s x‖ < e) :
    ∀ e : ℝ, 0 < e → ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x, R ≤ ‖x‖ →
      (1 + ‖x‖) * ‖heatDuhamelGradient f t x‖ < e := by
  intro e he
  let d := e / (2 * Real.sqrt T + 1)
  have hd : 0 < d := by dsimp [d]; positivity
  obtain ⟨R, hR⟩ := heatGradientKernel_weighted_vanishes_uniformly
    (f := fun s : Icc 0 T => f s.1) (T := T)
    (fun s => hf s.1 s.2) (fun s => hbound s.1 s.2)
    (fun a ha => by
      obtain ⟨R, hR⟩ := hend a ha
      exact ⟨R, fun s => hR s.1 s.2⟩) d hd
  refine ⟨R, fun t ht x hx => ?_⟩
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  let B (s : ℝ) := d * (t - s) ^ (-(1 / 2 : ℝ))
  have hB : IntervalIntegrable B volume 0 t :=
    (intervalIntegrable_backwards_invSqrt t).const_mul d
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖(1 + ‖x‖) • heatGradientKernel (t - s) (f s) x‖ ≤ B s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    by_cases hst : s < t
    · exact hR ⟨s, hs.1.le, hs.2.trans ht.2⟩ (t - s)
        ⟨sub_pos.mpr hst, (sub_le_self t hs.1.le).trans ht.2⟩ x hx
    · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp only [heatGradientKernel, sub_self, mul_zero, Real.sqrt_zero, inv_zero,
        zero_smul, norm_zero, mul_zero]
      exact mul_nonneg hd.le (Real.rpow_nonneg (by simp) _)
  have h := intervalIntegral.norm_integral_le_of_norm_le ht.1
    (Eventually.of_forall hb) hB
  rw [intervalIntegral.integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw] at h
  change (1 + ‖x‖) * ‖heatDuhamelGradient f t x‖ ≤ ∫ s in (0 : ℝ)..t, B s at h
  have hi : (∫ s in (0 : ℝ)..t, B s) = d * (2 * Real.sqrt t) := by
    rw [show B = fun s => d * (t - s) ^ (-(1 / 2 : ℝ)) from rfl,
      intervalIntegral.integral_const_mul, integral_backwards_invSqrt]
  rw [hi] at h
  have hdeq : d * (2 * Real.sqrt T + 1) = e := div_mul_cancel₀ _ (by positivity)
  have hdt := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ht.2) (show 0 ≤ 2 * d by positivity)
  nlinarith

end PoincareConjecture.M35.RadialGauge
