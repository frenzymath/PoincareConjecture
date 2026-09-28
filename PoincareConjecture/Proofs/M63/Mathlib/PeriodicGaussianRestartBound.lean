import PoincareConjecture.Proofs.M63.Mathlib.PeriodicGaussianDuhamel
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false

open Set MeasureTheory Filter
open scoped intervalIntegral

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem periodicGaussianHeat_restart_norm_bound
    {σ t ν A B C : ℝ} (hσ : 0 < σ) (hσt : σ ≤ t) (hν : 0 < ν)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (h h₁ h₂ hdot F F₁ G : ℝ → C(AddCircle L, E))
    (hh : ContinuousOn h (Icc σ t)) (hh₁ : ContinuousOn h₁ (Icc σ t))
    (hh₂ : ContinuousOn h₂ (Icc σ t)) (hhdot : ContinuousOn hdot (Icc σ t))
    (hx : ∀ r ∈ Icc σ t, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h r (y : AddCircle L)) (h₁ r (x : AddCircle L)) x)
    (hxx : ∀ r ∈ Icc σ t, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h₁ r (y : AddCircle L)) (h₂ r (x : AddCircle L)) x)
    (htime : ∀ r ∈ Ioo σ t, ∀ x : ℝ,
      HasDerivAt (fun s => h s (x : AddCircle L)) (hdot r (x : AddCircle L)) r)
    (hF : ∀ r ∈ Ioo σ t, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => F r (y : AddCircle L)) (F₁ r (x : AddCircle L)) x)
    (hforcing : ∀ r ∈ Ioo σ t, hdot r - ν • h₂ r = F₁ r + G r)
    (hFnorm : ∀ r ∈ Ioo σ t, ‖F r‖ ≤ A * Real.sqrt r)
    (hGnorm : ∀ r ∈ Ioo σ t, ‖G r‖ ≤ B + C / Real.sqrt r) :
    let Cν := (∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖) / (2 * Real.sqrt ν)
    ‖h t - periodicGaussianHeat (ν * (t - σ)) (h σ)‖ ≤
      (2 * Cν * A + B) * t + 2 * C * Real.sqrt t := by
  dsimp only
  let D := ∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖
  let Cν := D / (2 * Real.sqrt ν)
  let R : ℝ → C(AddCircle L, E) := fun r =>
    periodicGaussianHeat (ν * (t - r)) (hdot r - ν • h₂ r)
  let M : ℝ → ℝ := fun r =>
    (Cν * A * Real.sqrt t) * (t - r) ^ (-(1 / 2 : ℝ)) +
      B + C * r ^ (-(1 / 2 : ℝ))
  have hD : 0 ≤ D := integral_nonneg fun _ => norm_nonneg _
  have hCν : 0 ≤ Cν := div_nonneg hD (by positivity)
  have ht : 0 < t := hσ.trans_le hσt
  have hpow (r : ℝ) (hr : 0 ≤ r) : r ^ (-(1 / 2 : ℝ)) = (Real.sqrt r)⁻¹ := by
    rw [Real.rpow_neg hr, ← Real.sqrt_eq_rpow]
  have hpoint (r : ℝ) (hr : r ∈ Ioo σ t) : ‖R r‖ ≤ M r := by
    have hr0 : 0 < r := hσ.trans hr.1
    have hlag : 0 < t - r := sub_pos.mpr hr.2
    have hcoef : D / (2 * Real.sqrt (ν * (t - r))) = Cν / Real.sqrt (t - r) := by
      rw [Real.sqrt_mul hν.le]
      dsimp only [Cν]
      ring
    have hgrad := (periodicGaussianHeat_derivative_formula_bound
      (mul_pos hν hlag) (F r) (F₁ r) (hF r hr)).2
    have hcontract := (periodicGaussianHeat_properties (G r)).1 (ν * (t - r))
    change ‖periodicGaussianHeat (ν * (t - r)) (F₁ r)‖ ≤
      (D / (2 * Real.sqrt (ν * (t - r)))) * ‖F r‖ at hgrad
    rw [hcoef] at hgrad
    calc
      ‖R r‖ = ‖periodicGaussianHeat (ν * (t - r)) (F₁ r) +
          periodicGaussianHeat (ν * (t - r)) (G r)‖ := by
        dsimp only [R]
        rw [hforcing r hr, map_add]
      _ ≤ ‖periodicGaussianHeat (ν * (t - r)) (F₁ r)‖ +
          ‖periodicGaussianHeat (ν * (t - r)) (G r)‖ := norm_add_le _ _
      _ ≤ (Cν / Real.sqrt (t - r)) * ‖F r‖ + ‖G r‖ := add_le_add hgrad hcontract
      _ ≤ (Cν / Real.sqrt (t - r)) * (A * Real.sqrt r) +
          (B + C / Real.sqrt r) :=
        add_le_add (mul_le_mul_of_nonneg_left (hFnorm r hr) (by positivity)) (hGnorm r hr)
      _ ≤ (Cν / Real.sqrt (t - r)) * (A * Real.sqrt t) +
          (B + C / Real.sqrt r) := by
        gcongr
        exact hr.2.le
      _ = M r := by
        dsimp only [M]
        rw [hpow (t - r) hlag.le, hpow r hr0.le]
        ring
  have hp1 : IntervalIntegrable (fun r : ℝ => (t - r) ^ (-(1 / 2 : ℝ))) volume σ t := by
    simpa only [sub_zero, sub_sub_cancel] using
      ((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := t - σ)
        (r := -(1 / 2 : ℝ)) (by norm_num)).comp_sub_left t).symm
  have hp2 : IntervalIntegrable (fun r : ℝ => r ^ (-(1 / 2 : ℝ))) volume σ t :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have hM : IntervalIntegrable M volume σ t :=
    ((hp1.const_mul _).add intervalIntegrable_const).add (hp2.const_mul _)
  have hnorm : ‖∫ r in σ..t, R r‖ ≤ ∫ r in σ..t, M r :=
    intervalIntegral.norm_integral_le_of_norm_le hσt (by
      filter_upwards [volume.ae_ne t] with r hrt
      intro hr
      exact hpoint r ⟨hr.1, lt_of_le_of_ne hr.2 hrt⟩) hM
  have hp1I : (∫ r in σ..t, (t - r) ^ (-(1 / 2 : ℝ))) = 2 * Real.sqrt (t - σ) := by
    rw [intervalIntegral.integral_comp_sub_left
      (f := fun r : ℝ => r ^ (-(1 / 2 : ℝ))) t, sub_self,
      integral_rpow (Or.inl (by norm_num))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  have hp2I : (∫ r in σ..t, r ^ (-(1 / 2 : ℝ))) =
      2 * (Real.sqrt t - Real.sqrt σ) := by
    rw [integral_rpow (Or.inl (by norm_num))]
    norm_num [← Real.sqrt_eq_rpow]
    ring
  have hMI : (∫ r in σ..t, M r) =
      2 * Cν * A * Real.sqrt t * Real.sqrt (t - σ) +
        B * (t - σ) + 2 * C * (Real.sqrt t - Real.sqrt σ) := by
    dsimp only [M]
    rw [intervalIntegral.integral_add
      ((hp1.const_mul _).add intervalIntegrable_const) (hp2.const_mul _),
      intervalIntegral.integral_add (hp1.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul, hp1I, hp2I]
    simp only [smul_eq_mul]
    ring
  have hfirst : 2 * Cν * A * Real.sqrt t * Real.sqrt (t - σ) ≤ 2 * Cν * A * t := by
    calc
      _ ≤ 2 * Cν * A * Real.sqrt t * Real.sqrt t := by
        gcongr
        exact sub_le_self t hσ.le
      _ = _ := by rw [mul_assoc, ← sq, Real.sq_sqrt ht.le]
  have hsecond : B * (t - σ) ≤ B * t :=
    mul_le_mul_of_nonneg_left (sub_le_self t hσ.le) hB
  have hthird : 2 * C * (Real.sqrt t - Real.sqrt σ) ≤ 2 * C * Real.sqrt t :=
    mul_le_mul_of_nonneg_left (sub_le_self _ (Real.sqrt_nonneg _)) (by positivity)
  have hduh := periodicGaussianHeat_duhamel_of_derivative_witnesses hσt hν
    h h₁ h₂ hdot hh hh₁ hh₂ hhdot hx hxx htime (t := t) ⟨hσt, le_rfl⟩
  have heq : h t - periodicGaussianHeat (ν * (t - σ)) (h σ) = ∫ r in σ..t, R r := by
    rw [hduh]
    dsimp only [R]
    abel
  change ‖h t - periodicGaussianHeat (ν * (t - σ)) (h σ)‖ ≤
    (2 * Cν * A + B) * t + 2 * C * Real.sqrt t
  rw [heq]
  exact hnorm.trans (hMI.le.trans (by nlinarith only [hfirst, hsecond, hthird]))

end PoincareConjecture.M63
