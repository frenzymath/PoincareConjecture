import PoincareConjecture.Proofs.M35.RadialGauge.HeatGradient
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

local notation "V" => EuclideanSpace ℝ (Fin n)


noncomputable def heatDuhamel (f : ℝ → V → F) (t : ℝ) (x : V) : F :=
  ∫ s in (0 : ℝ)..t, heatAverage (t - s) (f s) x


noncomputable def heatDuhamelGradient (f : ℝ → V → F) (t : ℝ) (x : V) : V →L[ℝ] F :=
  ∫ s in (0 : ℝ)..t, heatGradientKernel (t - s) (f s) x



theorem intervalIntegrable_backwards_invSqrt (t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(1 / 2 : ℝ))) volume 0 t := by
  have h := (intervalIntegral.intervalIntegrable_rpow'
    (a := 0) (b := t) (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t
  simpa using h.symm


theorem integral_backwards_invSqrt (t : ℝ) :
    (∫ s in (0 : ℝ)..t, (t - s) ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt t := by
  rw [intervalIntegral.integral_comp_sub_left (f := fun r : ℝ => r ^ (-(1 / 2 : ℝ))) t]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 / 2 : ℝ)))]
  norm_num [← Real.sqrt_eq_rpow]
  ring



theorem heatGradientKernel_weighted_norm_le_rpow {f : V → F} (hf : Continuous f)
    {C t : ℝ} (hC : 0 ≤ C) (hbound : ∀ x, (1 + ‖x‖) * ‖f x‖ ≤ C)
    (ht : 0 < t) (x : V) :
    (1 + ‖x‖) * ‖heatGradientKernel t f x‖ ≤
      C * (gaussianFirstMoment n * t ^ (-(1 / 2 : ℝ)) + gaussianSecondMoment n) := by
  apply (heatGradientKernel_weighted_norm_le hf hbound ht x).trans
  apply mul_le_mul_of_nonneg_left _ hC
  apply add_le_add _ le_rfl
  rw [div_eq_mul_inv]
  apply mul_le_mul_of_nonneg_left _ gaussianFirstMoment_nonneg
  rw [Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow]
  apply (inv_le_inv₀ (by positivity) (Real.sqrt_pos.mpr ht)).mpr
  exact Real.sqrt_le_sqrt (by linarith)



theorem heatDuhamel_weighted_norm_le {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    (1 + ‖x‖) * ‖heatDuhamel f t x‖ ≤
      C * t * (1 + Real.sqrt (2 * t) * gaussianFirstMoment n) := by
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t)
    (f := fun s => (1 + ‖x‖) • heatAverage (t - s) (f s) x)
    (C := C * (1 + Real.sqrt (2 * t) * gaussianFirstMoment n)) (by
      intro s hs
      rw [uIoc_of_le ht] at hs
      have hs' : s ∈ Icc 0 t := ⟨hs.1.le, hs.2⟩
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
      exact heatAverage_weighted_norm_le_on_slab (hf s hs') hC (hbound s hs')
        ⟨sub_nonneg.mpr hs.2, sub_le_self _ hs.1.le⟩ x)
  rw [intervalIntegral.integral_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hw, sub_zero, abs_of_nonneg ht] at h
  change (1 + ‖x‖) * ‖heatDuhamel f t x‖ ≤ _ at h
  nlinarith [h]



theorem heatDuhamelGradient_weighted_norm_le {f : ℝ → V → F} {C t : ℝ}
    (hC : 0 ≤ C) (ht : 0 ≤ t)
    (hf : ∀ s ∈ Icc 0 t, Continuous (f s))
    (hbound : ∀ s ∈ Icc 0 t, ∀ x, (1 + ‖x‖) * ‖f s x‖ ≤ C) (x : V) :
    (1 + ‖x‖) * ‖heatDuhamelGradient f t x‖ ≤
      C * (2 * gaussianFirstMoment n * Real.sqrt t + gaussianSecondMoment n * t) := by
  have hw : 0 ≤ 1 + ‖x‖ := by positivity
  let B (s : ℝ) := C * (gaussianFirstMoment n * (t - s) ^ (-(1 / 2 : ℝ)) +
    gaussianSecondMoment n)
  have hB : IntervalIntegrable B volume 0 t :=
    (((intervalIntegrable_backwards_invSqrt t).const_mul (gaussianFirstMoment n)).add
      (intervalIntegrable_const)).const_mul C
  have hb (s : ℝ) (hs : s ∈ Ioc 0 t) :
      ‖(1 + ‖x‖) • heatGradientKernel (t - s) (f s) x‖ ≤ B s := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw]
    by_cases hst : s < t
    · have hd : 0 < t - s := sub_pos.mpr hst
      exact heatGradientKernel_weighted_norm_le_rpow (hf s ⟨hs.1.le, hs.2⟩)
        hC (hbound s ⟨hs.1.le, hs.2⟩) hd x
    · have hst' : s = t := le_antisymm hs.2 (le_of_not_gt hst)
      subst s
      simp only [heatGradientKernel, sub_self, mul_zero, Real.sqrt_zero, inv_zero,
        zero_smul, norm_zero, mul_zero]
      exact mul_nonneg hC (add_nonneg
        (mul_nonneg gaussianFirstMoment_nonneg (Real.rpow_nonneg (by simp) _))
        gaussianSecondMoment_nonneg)
  have h := intervalIntegral.norm_integral_le_of_norm_le ht
    (Eventually.of_forall hb) hB
  rw [intervalIntegral.integral_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hw] at h
  change (1 + ‖x‖) * ‖heatDuhamelGradient f t x‖ ≤ ∫ s in (0 : ℝ)..t, B s at h
  convert! h using 1
  dsimp only [B]
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add
      ((intervalIntegrable_backwards_invSqrt t).const_mul (gaussianFirstMoment n))
      intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_backwards_invSqrt]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring

end PoincareConjecture.M35.RadialGauge
