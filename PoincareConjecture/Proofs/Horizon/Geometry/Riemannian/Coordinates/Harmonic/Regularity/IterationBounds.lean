import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real









noncomputable section

set_option autoImplicit false

open Finset

namespace PoincareConjecture.HarmonicCoordinates


theorem geometric_iteration_bound_exp {χ D L : ℝ}
    (hχ : 1 < χ) (hD : 1 ≤ D) (hL : 1 ≤ L)
    {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ (D * L ^ k) ^ (1 / (2 * χ ^ k)) * u k)
    (k : ℕ) :
    u k ≤ Real.exp ((Real.log D / 2) * (1 - χ⁻¹)⁻¹ +
      (Real.log L / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) * u 0 := by
  have hχ0 : 0 < χ := lt_trans zero_lt_one hχ
  have hD0 : 0 < D := zero_lt_one.trans_le hD
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let r := χ⁻¹
  have hr0 : 0 ≤ r := (inv_pos.mpr hχ0).le
  have hr1 : r < 1 := inv_lt_one_of_one_lt₀ hχ
  have hrnorm : ‖r‖ < 1 := by simpa only [Real.norm_of_nonneg hr0] using hr1
  let a : ℕ → ℝ := fun k => (Real.log D + (k : ℝ) * Real.log L) / (2 * χ ^ k)
  let S := (Real.log D / 2) * (1 - r)⁻¹ +
    (Real.log L / 2) * (r / (1 - r) ^ 2)
  have ha (k : ℕ) : 0 ≤ a k := by
    dsimp only [a]
    exact div_nonneg (add_nonneg (Real.log_nonneg hD)
      (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hL))) (by positivity)
  have hsum : HasSum a S := by
    convert! ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (Real.log D / 2)).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hrnorm).mul_left (Real.log L / 2)) using 1
    ext k
    dsimp only [a, r]
    simp only [div_eq_mul_inv, mul_inv_rev, inv_pow]
    ring
  have hpartial (k : ℕ) : ∑ j ∈ range k, a j ≤ S :=
    sum_le_hasSum (range k) (fun j _ => ha j) hsum
  have hfactor (j : ℕ) : (D * L ^ j) ^ (1 / (2 * χ ^ j)) = Real.exp (a j) := by
    rw [Real.rpow_def_of_pos (mul_pos hD0 (pow_pos hL0 j)),
      Real.log_mul hD0.ne' (pow_ne_zero j hL0.ne'), Real.log_pow]
    congr 1
    dsimp only [a]
    ring
  have hprefix (j : ℕ) : u j ≤ Real.exp (∑ i ∈ range j, a i) * u 0 := by
    induction j with
    | zero => simp only [range_zero, sum_empty, Real.exp_zero, one_mul, le_refl]
    | succ j ih =>
      calc
        u (j + 1) ≤ Real.exp (a j) * u j := by simpa only [hfactor] using hstep j
        _ ≤ Real.exp (a j) * (Real.exp (∑ i ∈ range j, a i) * u 0) :=
          mul_le_mul_of_nonneg_left ih (Real.exp_pos _).le
        _ = Real.exp (∑ i ∈ range (j + 1), a i) * u 0 := by
          rw [sum_range_succ, Real.exp_add]
          ring
  exact (hprefix k).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hpartial k)) (hu 0))


theorem exists_uniform_geometric_iteration_bound {χ D L : ℝ}
    (hχ : 1 < χ) (hD : 1 ≤ D) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℕ → ℝ, (∀ k, 0 ≤ u k) →
      (∀ k, u (k + 1) ≤ (D * L ^ k) ^ (1 / (2 * χ ^ k)) * u k) →
      ∀ k, u k ≤ C * u 0 := by
  let C := Real.exp ((Real.log D / 2) * (1 - χ⁻¹)⁻¹ +
    (Real.log L / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2))
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro u hu hstep k
  exact (geometric_iteration_bound_exp hχ hD hL hu hstep k).trans
    (mul_le_mul_of_nonneg_right (le_max_right _ _) (hu 0))



theorem geometric_iteration_bound_rpow {χ D L : ℝ}
    (hχ : 1 < χ) (hD : 1 ≤ D) (hL : 1 ≤ L)
    {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k)
    (hstep : ∀ k, u (k + 1) ≤ (D * L ^ k) ^ (1 / (2 * χ ^ k)) * u k)
    (k : ℕ) :
    u k ≤ (D ^ (χ / (2 * (χ - 1))) * L ^ (χ / (2 * (χ - 1) ^ 2))) * u 0 := by
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  have hχ1 : χ - 1 ≠ 0 := (sub_pos.mpr hχ).ne'
  have hexp : Real.exp ((Real.log D / 2) * (1 - χ⁻¹)⁻¹ +
      (Real.log L / 2) * (χ⁻¹ / (1 - χ⁻¹) ^ 2)) =
      D ^ (χ / (2 * (χ - 1))) * L ^ (χ / (2 * (χ - 1) ^ 2)) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans_le hD),
      Real.rpow_def_of_pos (zero_lt_one.trans_le hL), ← Real.exp_add]
    congr 1
    field_simp [hχ0.ne', hχ1]
  simpa only [hexp] using geometric_iteration_bound_exp hχ hD hL hu hstep k



theorem exists_uniform_scaled_iteration_bound {χ D L : ℝ}
    (hχ : 1 < χ) (hD : 1 ≤ D) (hL : 1 ≤ L) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ, 0 < r → r ≤ 1 →
      ∀ u : ℕ → ℝ, (∀ k, 0 ≤ u k) →
        (∀ k, u (k + 1) ≤ ((D / r) * L ^ k) ^ (1 / (2 * χ ^ k)) * u k) →
        ∀ k, u k ≤ C * r ^ (-(χ / (2 * (χ - 1)))) * u 0 := by
  let α := χ / (2 * (χ - 1))
  let β := χ / (2 * (χ - 1) ^ 2)
  have hχ0 : 0 < χ := zero_lt_one.trans hχ
  have hχm : 0 < χ - 1 := sub_pos.mpr hχ
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; positivity
  have hC : 1 ≤ D ^ α * L ^ β :=
    one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hD hα) (Real.one_le_rpow hL hβ)
  refine ⟨D ^ α * L ^ β, hC, ?_⟩
  intro r hr hr1 u hu hstep k
  have hDr : 1 ≤ D / r := (le_div_iff₀ hr).mpr (by simpa using hr1.trans hD)
  have h := geometric_iteration_bound_rpow hχ hDr hL hu hstep k
  change u k ≤ ((D / r) ^ α * L ^ β) * u 0 at h
  change u k ≤ (D ^ α * L ^ β) * r ^ (-α) * u 0
  rw [Real.div_rpow (zero_lt_one.trans_le hD).le hr.le] at h
  simpa only [Real.rpow_neg hr.le, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

end PoincareConjecture.HarmonicCoordinates
