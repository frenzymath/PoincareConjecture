import PoincareConjecture.Proofs.M35.RadialGauge.ScalarRapidProducts










set_option autoImplicit false

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M35.RadialGauge



theorem scalar_weighted_product {A : Type*} {f g : A → ℝ → ℝ} {N : ℕ}
    (hf : ∀ a, ContDiffOn ℝ ∞ (f a) (Ioi 0))
    (hg : ∀ a, ContDiffOn ℝ ∞ (g a) (Ioi 0))
    (hb : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      |iteratedDeriv j (f a) r| ≤ C)
    (hr : ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (g a) r| ≤ C) :
    ∀ j : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a r, 1 ≤ r →
      (1 + r) ^ N * |iteratedDeriv j (fun s => f a s * g a s) r| ≤ C := by
  classical
  choose B hB0 hB using hb
  choose D hD0 hD using hr
  intro j
  let C := ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * B i * D (j - i)
  refine ⟨C, Finset.sum_nonneg (fun i _ =>
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hB0 i)) (hD0 (j - i))), ?_⟩
  intro a r hrad
  have hpos : 0 < r := lt_of_lt_of_le zero_lt_one hrad
  have hfa := ((hf a) r hpos).contDiffAt (Ioi_mem_nhds hpos)
  have hga := ((hg a) r hpos).contDiffAt (Ioi_mem_nhds hpos)
  rw [iteratedDeriv_fun_mul (hfa.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))
    (hga.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl j))]
  have hw : 0 ≤ (1 + r) ^ N := by positivity
  apply (mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  have hm := mul_le_mul
    (mul_le_mul_of_nonneg_left (hB i a r hrad) (Nat.cast_nonneg (j.choose i)))
    (hD (j - i) a r hrad) (mul_nonneg hw (abs_nonneg _))
    (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
  convert! hm using 1
  ring



theorem reciprocal_radius_weighted_jet_bound (j : ℕ) {r : ℝ} (hr : 1 ≤ r) :
    (1 + r) * |iteratedDeriv j (fun s : ℝ => 1 / s) r| ≤ 2 * (j.factorial : ℝ) := by
  have hrp : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hformula := iteratedDerivWithin_one_div (𝕜 := ℝ) j isOpen_univ (mem_univ r)
  simp only [iteratedDerivWithin_univ] at hformula
  rw [hformula, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg (zpow_nonneg hrp.le _)]
  have hp : r ^ (-1 - (j : ℤ)) ≤ r⁻¹ := by
    simpa only [zpow_neg_one] using
      zpow_le_zpow_right₀ hr (show (-1 - (j : ℤ)) ≤ -1 by omega)
  have hratio : (1 + r) * r⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv]
    exact (div_le_iff₀ hrp).mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_left hp
    (show 0 ≤ (1 + r) * (j.factorial : ℝ) by positivity)
  have hlast := mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg j.factorial)
  nlinarith only [hmul, hlast]

end PoincareConjecture.M35.RadialGauge
