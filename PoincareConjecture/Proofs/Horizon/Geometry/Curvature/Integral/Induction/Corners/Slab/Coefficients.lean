import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic



open Set
namespace Poincare.CurvatureIntegral
theorem exists_uniform_slab_coefficient (d : ℕ) {ℓ V H : ℝ}
    (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) (hV : 0 ≤ V) (hH : 0 ≤ H) :
    ∃ α : ℝ, 0 < α ∧ 1 / α ≤ 1 / 2 ∧
      ∀ r : ℝ, 0 < r → ∀ t ∈ Icc (3 * (ℓ * r) / 64) (15 * (ℓ * r) / 128),
        V * r ^ d ≤ α * t ^ d ∧ 2 * H / r ≤ α / t := by
  let c := 64 / (3 * ℓ)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  let α := 2 + 2 * H + V * c ^ d
  have hα2 : 2 ≤ α := by dsimp [α]; nlinarith [mul_nonneg hV (pow_nonneg hc d)]
  have hα : 0 < α := lt_of_lt_of_le (by norm_num) hα2
  refine ⟨α, hα, (one_div_le_one_div_of_le (by norm_num) hα2), ?_⟩
  intro r hr t ht
  have htpos : 0 < t := lt_of_lt_of_le (by positivity) ht.1
  have htr : t ≤ r := by
    have hh := mul_le_mul_of_nonneg_right hℓ1 hr.le
    nlinarith [ht.2]
  have hrc : r ≤ c * t := by
    have hden : 0 < 3 * ℓ := by positivity
    have hh : r * (3 * ℓ) ≤ 64 * t := by linarith [ht.1]
    dsimp [c]
    simpa only [div_mul_eq_mul_div] using (le_div_iff₀ hden).mpr hh
  constructor
  · calc
      V * r ^ d ≤ V * (c * t) ^ d :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrc d) hV
      _ = V * c ^ d * t ^ d := by rw [mul_pow]; ring
      _ ≤ α * t ^ d := mul_le_mul_of_nonneg_right (by dsimp [α]; linarith)
        (pow_nonneg htpos.le d)
  · apply (div_le_div_iff₀ hr htpos).mpr
    have hh := mul_le_mul_of_nonneg_left htr (by positivity : 0 ≤ 2 * H)
    have hh' : 2 * H ≤ α := by dsimp [α]; nlinarith [mul_nonneg hV (pow_nonneg hc d)]
    nlinarith [mul_le_mul_of_nonneg_right hh' hr.le]

theorem scaled_component_slab_remainder_le
    {m : ℕ} (hm : 1 ≤ m) {α C D P b r : ℝ}
    (hα : 0 ≤ α) (hC : 0 ≤ C) (hD : 0 ≤ D) (hP : 0 ≤ P)
    (hb : 0 ≤ b) (hbr : 3 * b / 2 ≤ r) (N : ℕ) :
    3 * α * C * ((N : ℝ) * (D * r) ^ (m - 1)) * b +
        2 * P * (3 * b / 2) ^ m + 4 * α * b ^ m ≤
      (3 * α * C * (N : ℝ) * D ^ (m - 1) + 2 * P + 4 * α) * r ^ m := by
  have hr : 0 ≤ r := (by positivity : 0 ≤ 3 * b / 2).trans hbr
  have hbr' : b ≤ r := by linarith
  have hpowb : b ^ m ≤ r ^ m := pow_le_pow_left₀ hb hbr' m
  have hpowouter : (3 * b / 2) ^ m ≤ r ^ m :=
    pow_le_pow_left₀ (by positivity) hbr m
  have hfirst : (D * r) ^ (m - 1) * b ≤ D ^ (m - 1) * r ^ m := by
    calc
      _ ≤ (D * r) ^ (m - 1) * r :=
        mul_le_mul_of_nonneg_left hbr' (by positivity)
      _ = _ := by
        rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hm]
  have h1 := mul_le_mul_of_nonneg_left hfirst
    (by positivity : 0 ≤ 3 * α * C * (N : ℝ))
  have h2 := mul_le_mul_of_nonneg_left hpowouter (by positivity : 0 ≤ 2 * P)
  have h3 := mul_le_mul_of_nonneg_left hpowb (by positivity : 0 ≤ 4 * α)
  nlinarith only [h1, h2, h3]
end Poincare.CurvatureIntegral
